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
Require Import SimpleC.EE.coins_101.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import ptr_array2_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import ptr_array2_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_proof.
From SimpleC.StdLib Require Import string_strategy_goal.
From SimpleC.StdLib Require Import string_strategy_proof.

(*----- Function words_string -----*)

Definition words_string_safety_wit_1 := 
forall (s_pre: Z) (input_ptr: Z) (input: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (s_pre = input_ptr)) (PreH4 : (problem_101_pre_z input )) (PreH5 : (valid_string input )) (PreH6 : ((2 * ((string_length (input)) + 1 ) ) < INT_MAX)) ,
  ((( &( "output_size" ) )) # Int  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (CharArray.full s_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition words_string_safety_wit_2 := 
forall (s_pre: Z) (input_ptr: Z) (input: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (s_pre = input_ptr)) (PreH4 : (problem_101_pre_z input )) (PreH5 : (valid_string input )) (PreH6 : ((2 * ((string_length (input)) + 1 ) ) < INT_MAX)) ,
  ((( &( "start" ) )) # Int  |->_)
  **  ((( &( "output_size" ) )) # Int  |-> 0)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (CharArray.full s_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition words_string_safety_wit_3 := 
forall (s_pre: Z) (input_ptr: Z) (input: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (s_pre = input_ptr)) (PreH4 : (problem_101_pre_z input )) (PreH5 : (valid_string input )) (PreH6 : ((2 * ((string_length (input)) + 1 ) ) < INT_MAX)) ,
  ((( &( "start" ) )) # Int  |->_)
  **  ((( &( "output_size" ) )) # Int  |-> 0)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (CharArray.full s_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition words_string_safety_wit_4 := 
forall (s_pre: Z) (input_ptr: Z) (input: (@list Z)) (retval_2: Z) (retval: Z) (PreH1 : (retval = (string_length (input)))) (PreH2 : (retval_2 <> 0)) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (s_pre = input_ptr)) (PreH5 : (problem_101_pre_z input )) (PreH6 : (valid_string input )) (PreH7 : ((2 * ((string_length (input)) + 1 ) ) < INT_MAX)) ,
  ((( &( "cap" ) )) # Int  |->_)
  **  (store_string s_pre input )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "start" ) )) # Int  |-> (-1))
  **  ((( &( "output_size" ) )) # Int  |-> 0)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ ((retval + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval + 1 )) ”
.

Definition words_string_safety_wit_5 := 
forall (s_pre: Z) (input_ptr: Z) (input: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (string_length (input)))) (PreH2 : (retval <> 0)) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (s_pre = input_ptr)) (PreH5 : (problem_101_pre_z input )) (PreH6 : (valid_string input )) (PreH7 : ((2 * ((string_length (input)) + 1 ) ) < INT_MAX)) ,
  ((( &( "cap" ) )) # Int  |->_)
  **  (store_string s_pre input )
  **  ((( &( "n" ) )) # Int  |-> retval_2)
  **  ((( &( "start" ) )) # Int  |-> (-1))
  **  ((( &( "output_size" ) )) # Int  |-> 0)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition words_string_safety_wit_6 := 
forall (s_pre: Z) (input_ptr: Z) (input: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 = (string_length (input)))) (PreH3 : (retval <> 0)) (PreH4 : (0 <= ((string_length (input)) + 1 ))) (PreH5 : (s_pre = input_ptr)) (PreH6 : (problem_101_pre_z input )) (PreH7 : (valid_string input )) (PreH8 : ((2 * ((string_length (input)) + 1 ) ) < INT_MAX)) ,
  (PtrArray.undef_seg retval_3 0 (retval_2 + 1 ) )
  **  (CharArray.full s_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "data" ) )) # Ptr  |-> retval_3)
  **  ((( &( "cap" ) )) # Int  |-> (retval_2 + 1 ))
  **  ((( &( "n" ) )) # Int  |-> retval_2)
  **  ((( &( "start" ) )) # Int  |-> (-1))
  **  ((( &( "output_size" ) )) # Int  |-> 0)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_3)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition words_string_safety_wit_7 := 
forall (s_pre: Z) (input_ptr: Z) (input: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 = (string_length (input)))) (PreH3 : (retval <> 0)) (PreH4 : (0 <= ((string_length (input)) + 1 ))) (PreH5 : (s_pre = input_ptr)) (PreH6 : (problem_101_pre_z input )) (PreH7 : (valid_string input )) (PreH8 : ((2 * ((string_length (input)) + 1 ) ) < INT_MAX)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  (PtrArray.undef_seg retval_3 0 (retval_2 + 1 ) )
  **  (CharArray.full s_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "data" ) )) # Ptr  |-> retval_3)
  **  ((( &( "cap" ) )) # Int  |-> (retval_2 + 1 ))
  **  ((( &( "n" ) )) # Int  |-> retval_2)
  **  ((( &( "start" ) )) # Int  |-> (-1))
  **  ((( &( "output_size" ) )) # Int  |-> 0)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_3)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition words_string_safety_wit_8 := 
forall (input_ptr: Z) (input: (@list Z)) (start: Z) (data: Z) (out: Z) (cap: Z) (output_ptrs: (@list Z)) (output_words: (@list (@list Z))) (output_size: Z) (n: Z) (i: Z) (PreH1 : (i >= n)) (PreH2 : (i <= n)) (PreH3 : (0 <= i)) (PreH4 : (i <= (n + 1 ))) (PreH5 : (n = (string_length (input)))) (PreH6 : (0 <= output_size)) (PreH7 : (output_size <= i)) (PreH8 : (output_size = (Zlength (output_words)))) (PreH9 : (output_size = (Zlength (output_ptrs)))) (PreH10 : (cap = (n + 1 ))) (PreH11 : (0 <= cap)) (PreH12 : (cap < INT_MAX)) (PreH13 : (output_size <= cap)) (PreH14 : (out <> 0)) (PreH15 : (data <> 0)) (PreH16 : (split_prefix_state_101 input i start output_words )) (PreH17 : (problem_101_pre_z input )) (PreH18 : (valid_string input )) (PreH19 : ((2 * ((string_length (input)) + 1 ) ) < INT_MAX)) ,
  ((( &( "ch" ) )) # Char  |->_)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "s" ) )) # Ptr  |-> input_ptr)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (store_string input_ptr input )
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size cap )
  **  (words_rows_heap_101 output_ptrs output_words )
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition words_string_safety_wit_9 := 
forall (input_ptr: Z) (input: (@list Z)) (start: Z) (data: Z) (out: Z) (cap: Z) (output_ptrs: (@list Z)) (output_words: (@list (@list Z))) (output_size: Z) (n: Z) (i: Z) (PreH1 : (i < n)) (PreH2 : (i <= n)) (PreH3 : (0 <= i)) (PreH4 : (i <= (n + 1 ))) (PreH5 : (n = (string_length (input)))) (PreH6 : (0 <= output_size)) (PreH7 : (output_size <= i)) (PreH8 : (output_size = (Zlength (output_words)))) (PreH9 : (output_size = (Zlength (output_ptrs)))) (PreH10 : (cap = (n + 1 ))) (PreH11 : (0 <= cap)) (PreH12 : (cap < INT_MAX)) (PreH13 : (output_size <= cap)) (PreH14 : (out <> 0)) (PreH15 : (data <> 0)) (PreH16 : (split_prefix_state_101 input i start output_words )) (PreH17 : (problem_101_pre_z input )) (PreH18 : (valid_string input )) (PreH19 : ((2 * ((string_length (input)) + 1 ) ) < INT_MAX)) ,
  ((( &( "ch" ) )) # Char  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "s" ) )) # Ptr  |-> input_ptr)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (store_string input_ptr input )
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size cap )
  **  (words_rows_heap_101 output_ptrs output_words )
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition words_string_safety_wit_10 := 
forall (input_ptr: Z) (input: (@list Z)) (start: Z) (data: Z) (out: Z) (cap: Z) (output_ptrs: (@list Z)) (output_words: (@list (@list Z))) (output_size: Z) (n: Z) (i: Z) (PreH1 : (i >= n)) (PreH2 : (i <= n)) (PreH3 : (0 <= i)) (PreH4 : (i <= (n + 1 ))) (PreH5 : (n = (string_length (input)))) (PreH6 : (0 <= output_size)) (PreH7 : (output_size <= i)) (PreH8 : (output_size = (Zlength (output_words)))) (PreH9 : (output_size = (Zlength (output_ptrs)))) (PreH10 : (cap = (n + 1 ))) (PreH11 : (0 <= cap)) (PreH12 : (cap < INT_MAX)) (PreH13 : (output_size <= cap)) (PreH14 : (out <> 0)) (PreH15 : (data <> 0)) (PreH16 : (split_prefix_state_101 input i start output_words )) (PreH17 : (problem_101_pre_z input )) (PreH18 : (valid_string input )) (PreH19 : ((2 * ((string_length (input)) + 1 ) ) < INT_MAX)) ,
  ((( &( "ch" ) )) # Char  |-> 32)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "s" ) )) # Ptr  |-> input_ptr)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (store_string input_ptr input )
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size cap )
  **  (words_rows_heap_101 output_ptrs output_words )
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition words_string_safety_wit_11 := 
forall (input_ptr: Z) (input: (@list Z)) (start: Z) (data: Z) (out: Z) (cap: Z) (output_ptrs: (@list Z)) (output_words: (@list (@list Z))) (output_size: Z) (n: Z) (i: Z) (PreH1 : ((Znth i (c_string (input)) 0) <> 32)) (PreH2 : (i < n)) (PreH3 : (i <= n)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n + 1 ))) (PreH6 : (n = (string_length (input)))) (PreH7 : (0 <= output_size)) (PreH8 : (output_size <= i)) (PreH9 : (output_size = (Zlength (output_words)))) (PreH10 : (output_size = (Zlength (output_ptrs)))) (PreH11 : (cap = (n + 1 ))) (PreH12 : (0 <= cap)) (PreH13 : (cap < INT_MAX)) (PreH14 : (output_size <= cap)) (PreH15 : (out <> 0)) (PreH16 : (data <> 0)) (PreH17 : (split_prefix_state_101 input i start output_words )) (PreH18 : (problem_101_pre_z input )) (PreH19 : (valid_string input )) (PreH20 : ((2 * ((string_length (input)) + 1 ) ) < INT_MAX)) ,
  ((( &( "ch" ) )) # Char  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "s" ) )) # Ptr  |-> input_ptr)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (store_string input_ptr input )
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size cap )
  **  (words_rows_heap_101 output_ptrs output_words )
|--
  “ (44 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 44) ”
.

Definition words_string_safety_wit_12 := 
forall (input_ptr: Z) (input: (@list Z)) (start: Z) (data: Z) (out: Z) (cap: Z) (output_ptrs: (@list Z)) (output_words: (@list (@list Z))) (output_size: Z) (n: Z) (i: Z) (PreH1 : (i >= n)) (PreH2 : (i <= n)) (PreH3 : (0 <= i)) (PreH4 : (i <= (n + 1 ))) (PreH5 : (n = (string_length (input)))) (PreH6 : (0 <= output_size)) (PreH7 : (output_size <= i)) (PreH8 : (output_size = (Zlength (output_words)))) (PreH9 : (output_size = (Zlength (output_ptrs)))) (PreH10 : (cap = (n + 1 ))) (PreH11 : (0 <= cap)) (PreH12 : (cap < INT_MAX)) (PreH13 : (output_size <= cap)) (PreH14 : (out <> 0)) (PreH15 : (data <> 0)) (PreH16 : (split_prefix_state_101 input i start output_words )) (PreH17 : (problem_101_pre_z input )) (PreH18 : (valid_string input )) (PreH19 : ((2 * ((string_length (input)) + 1 ) ) < INT_MAX)) ,
  ((( &( "ch" ) )) # Char  |-> 32)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "s" ) )) # Ptr  |-> input_ptr)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (store_string input_ptr input )
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size cap )
  **  (words_rows_heap_101 output_ptrs output_words )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition words_string_safety_wit_13 := 
forall (input_ptr: Z) (input: (@list Z)) (start: Z) (data: Z) (out: Z) (cap: Z) (output_ptrs: (@list Z)) (output_words: (@list (@list Z))) (output_size: Z) (n: Z) (i: Z) (PreH1 : ((Znth i (c_string (input)) 0) = 32)) (PreH2 : (i < n)) (PreH3 : (i <= n)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n + 1 ))) (PreH6 : (n = (string_length (input)))) (PreH7 : (0 <= output_size)) (PreH8 : (output_size <= i)) (PreH9 : (output_size = (Zlength (output_words)))) (PreH10 : (output_size = (Zlength (output_ptrs)))) (PreH11 : (cap = (n + 1 ))) (PreH12 : (0 <= cap)) (PreH13 : (cap < INT_MAX)) (PreH14 : (output_size <= cap)) (PreH15 : (out <> 0)) (PreH16 : (data <> 0)) (PreH17 : (split_prefix_state_101 input i start output_words )) (PreH18 : (problem_101_pre_z input )) (PreH19 : (valid_string input )) (PreH20 : ((2 * ((string_length (input)) + 1 ) ) < INT_MAX)) ,
  ((( &( "ch" ) )) # Char  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "s" ) )) # Ptr  |-> input_ptr)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (store_string input_ptr input )
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size cap )
  **  (words_rows_heap_101 output_ptrs output_words )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition words_string_safety_wit_14 := 
forall (input_ptr: Z) (input: (@list Z)) (start: Z) (data: Z) (out: Z) (cap: Z) (output_ptrs: (@list Z)) (output_words: (@list (@list Z))) (output_size: Z) (n: Z) (i: Z) (PreH1 : ((Znth i (c_string (input)) 0) = 44)) (PreH2 : ((Znth i (c_string (input)) 0) <> 32)) (PreH3 : (i < n)) (PreH4 : (i <= n)) (PreH5 : (0 <= i)) (PreH6 : (i <= (n + 1 ))) (PreH7 : (n = (string_length (input)))) (PreH8 : (0 <= output_size)) (PreH9 : (output_size <= i)) (PreH10 : (output_size = (Zlength (output_words)))) (PreH11 : (output_size = (Zlength (output_ptrs)))) (PreH12 : (cap = (n + 1 ))) (PreH13 : (0 <= cap)) (PreH14 : (cap < INT_MAX)) (PreH15 : (output_size <= cap)) (PreH16 : (out <> 0)) (PreH17 : (data <> 0)) (PreH18 : (split_prefix_state_101 input i start output_words )) (PreH19 : (problem_101_pre_z input )) (PreH20 : (valid_string input )) (PreH21 : ((2 * ((string_length (input)) + 1 ) ) < INT_MAX)) ,
  ((( &( "ch" ) )) # Char  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "s" ) )) # Ptr  |-> input_ptr)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (store_string input_ptr input )
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size cap )
  **  (words_rows_heap_101 output_ptrs output_words )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition words_string_safety_wit_15 := 
forall (input_ptr: Z) (input: (@list Z)) (start: Z) (data: Z) (out: Z) (cap: Z) (output_ptrs: (@list Z)) (output_words: (@list (@list Z))) (output_size: Z) (n: Z) (i: Z) (PreH1 : (start >= 0)) (PreH2 : (i >= n)) (PreH3 : (i <= n)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n + 1 ))) (PreH6 : (n = (string_length (input)))) (PreH7 : (0 <= output_size)) (PreH8 : (output_size <= i)) (PreH9 : (output_size = (Zlength (output_words)))) (PreH10 : (output_size = (Zlength (output_ptrs)))) (PreH11 : (cap = (n + 1 ))) (PreH12 : (0 <= cap)) (PreH13 : (cap < INT_MAX)) (PreH14 : (output_size <= cap)) (PreH15 : (out <> 0)) (PreH16 : (data <> 0)) (PreH17 : (split_prefix_state_101 input i start output_words )) (PreH18 : (problem_101_pre_z input )) (PreH19 : (valid_string input )) (PreH20 : ((2 * ((string_length (input)) + 1 ) ) < INT_MAX)) ,
  ((( &( "len" ) )) # Int  |->_)
  **  ((( &( "ch" ) )) # Char  |-> 32)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "s" ) )) # Ptr  |-> input_ptr)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (store_string input_ptr input )
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size cap )
  **  (words_rows_heap_101 output_ptrs output_words )
|--
  “ ((i - start ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - start )) ”
.

Definition words_string_safety_wit_16 := 
forall (input_ptr: Z) (input: (@list Z)) (start: Z) (data: Z) (out: Z) (cap: Z) (output_ptrs: (@list Z)) (output_words: (@list (@list Z))) (output_size: Z) (n: Z) (i: Z) (PreH1 : (start >= 0)) (PreH2 : ((Znth i (c_string (input)) 0) = 32)) (PreH3 : (i < n)) (PreH4 : (i <= n)) (PreH5 : (0 <= i)) (PreH6 : (i <= (n + 1 ))) (PreH7 : (n = (string_length (input)))) (PreH8 : (0 <= output_size)) (PreH9 : (output_size <= i)) (PreH10 : (output_size = (Zlength (output_words)))) (PreH11 : (output_size = (Zlength (output_ptrs)))) (PreH12 : (cap = (n + 1 ))) (PreH13 : (0 <= cap)) (PreH14 : (cap < INT_MAX)) (PreH15 : (output_size <= cap)) (PreH16 : (out <> 0)) (PreH17 : (data <> 0)) (PreH18 : (split_prefix_state_101 input i start output_words )) (PreH19 : (problem_101_pre_z input )) (PreH20 : (valid_string input )) (PreH21 : ((2 * ((string_length (input)) + 1 ) ) < INT_MAX)) ,
  ((( &( "len" ) )) # Int  |->_)
  **  ((( &( "ch" ) )) # Char  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "s" ) )) # Ptr  |-> input_ptr)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (store_string input_ptr input )
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size cap )
  **  (words_rows_heap_101 output_ptrs output_words )
|--
  “ ((i - start ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - start )) ”
.

Definition words_string_safety_wit_17 := 
forall (input_ptr: Z) (input: (@list Z)) (start: Z) (data: Z) (out: Z) (cap: Z) (output_ptrs: (@list Z)) (output_words: (@list (@list Z))) (output_size: Z) (n: Z) (i: Z) (PreH1 : (start >= 0)) (PreH2 : ((Znth i (c_string (input)) 0) = 44)) (PreH3 : ((Znth i (c_string (input)) 0) <> 32)) (PreH4 : (i < n)) (PreH5 : (i <= n)) (PreH6 : (0 <= i)) (PreH7 : (i <= (n + 1 ))) (PreH8 : (n = (string_length (input)))) (PreH9 : (0 <= output_size)) (PreH10 : (output_size <= i)) (PreH11 : (output_size = (Zlength (output_words)))) (PreH12 : (output_size = (Zlength (output_ptrs)))) (PreH13 : (cap = (n + 1 ))) (PreH14 : (0 <= cap)) (PreH15 : (cap < INT_MAX)) (PreH16 : (output_size <= cap)) (PreH17 : (out <> 0)) (PreH18 : (data <> 0)) (PreH19 : (split_prefix_state_101 input i start output_words )) (PreH20 : (problem_101_pre_z input )) (PreH21 : (valid_string input )) (PreH22 : ((2 * ((string_length (input)) + 1 ) ) < INT_MAX)) ,
  ((( &( "len" ) )) # Int  |->_)
  **  ((( &( "ch" ) )) # Char  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "s" ) )) # Ptr  |-> input_ptr)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (store_string input_ptr input )
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size cap )
  **  (words_rows_heap_101 output_ptrs output_words )
|--
  “ ((i - start ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - start )) ”
.

Definition words_string_safety_wit_18 := 
forall (input_ptr: Z) (input: (@list Z)) (start: Z) (data: Z) (out: Z) (cap: Z) (output_ptrs: (@list Z)) (output_words: (@list (@list Z))) (output_size: Z) (n: Z) (i: Z) (PreH1 : (start >= 0)) (PreH2 : (i >= n)) (PreH3 : (i <= n)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n + 1 ))) (PreH6 : (n = (string_length (input)))) (PreH7 : (0 <= output_size)) (PreH8 : (output_size <= i)) (PreH9 : (output_size = (Zlength (output_words)))) (PreH10 : (output_size = (Zlength (output_ptrs)))) (PreH11 : (cap = (n + 1 ))) (PreH12 : (0 <= cap)) (PreH13 : (cap < INT_MAX)) (PreH14 : (output_size <= cap)) (PreH15 : (out <> 0)) (PreH16 : (data <> 0)) (PreH17 : (split_prefix_state_101 input i start output_words )) (PreH18 : (problem_101_pre_z input )) (PreH19 : (valid_string input )) (PreH20 : ((2 * ((string_length (input)) + 1 ) ) < INT_MAX)) ,
  ((( &( "w" ) )) # Ptr  |->_)
  **  ((( &( "len" ) )) # Int  |-> (i - start ))
  **  ((( &( "ch" ) )) # Char  |-> 32)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "s" ) )) # Ptr  |-> input_ptr)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (store_string input_ptr input )
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size cap )
  **  (words_rows_heap_101 output_ptrs output_words )
|--
  “ (((i - start ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((i - start ) + 1 )) ”
.

Definition words_string_safety_wit_19 := 
forall (input_ptr: Z) (input: (@list Z)) (start: Z) (data: Z) (out: Z) (cap: Z) (output_ptrs: (@list Z)) (output_words: (@list (@list Z))) (output_size: Z) (n: Z) (i: Z) (PreH1 : (start >= 0)) (PreH2 : (i >= n)) (PreH3 : (i <= n)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n + 1 ))) (PreH6 : (n = (string_length (input)))) (PreH7 : (0 <= output_size)) (PreH8 : (output_size <= i)) (PreH9 : (output_size = (Zlength (output_words)))) (PreH10 : (output_size = (Zlength (output_ptrs)))) (PreH11 : (cap = (n + 1 ))) (PreH12 : (0 <= cap)) (PreH13 : (cap < INT_MAX)) (PreH14 : (output_size <= cap)) (PreH15 : (out <> 0)) (PreH16 : (data <> 0)) (PreH17 : (split_prefix_state_101 input i start output_words )) (PreH18 : (problem_101_pre_z input )) (PreH19 : (valid_string input )) (PreH20 : ((2 * ((string_length (input)) + 1 ) ) < INT_MAX)) ,
  ((( &( "w" ) )) # Ptr  |->_)
  **  ((( &( "len" ) )) # Int  |-> (i - start ))
  **  ((( &( "ch" ) )) # Char  |-> 32)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "s" ) )) # Ptr  |-> input_ptr)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (store_string input_ptr input )
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size cap )
  **  (words_rows_heap_101 output_ptrs output_words )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition words_string_safety_wit_20 := 
forall (input_ptr: Z) (input: (@list Z)) (start: Z) (data: Z) (out: Z) (cap: Z) (output_ptrs: (@list Z)) (output_words: (@list (@list Z))) (output_size: Z) (n: Z) (i: Z) (PreH1 : (start >= 0)) (PreH2 : ((Znth i (c_string (input)) 0) = 32)) (PreH3 : (i < n)) (PreH4 : (i <= n)) (PreH5 : (0 <= i)) (PreH6 : (i <= (n + 1 ))) (PreH7 : (n = (string_length (input)))) (PreH8 : (0 <= output_size)) (PreH9 : (output_size <= i)) (PreH10 : (output_size = (Zlength (output_words)))) (PreH11 : (output_size = (Zlength (output_ptrs)))) (PreH12 : (cap = (n + 1 ))) (PreH13 : (0 <= cap)) (PreH14 : (cap < INT_MAX)) (PreH15 : (output_size <= cap)) (PreH16 : (out <> 0)) (PreH17 : (data <> 0)) (PreH18 : (split_prefix_state_101 input i start output_words )) (PreH19 : (problem_101_pre_z input )) (PreH20 : (valid_string input )) (PreH21 : ((2 * ((string_length (input)) + 1 ) ) < INT_MAX)) ,
  ((( &( "w" ) )) # Ptr  |->_)
  **  ((( &( "len" ) )) # Int  |-> (i - start ))
  **  ((( &( "ch" ) )) # Char  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "s" ) )) # Ptr  |-> input_ptr)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (store_string input_ptr input )
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size cap )
  **  (words_rows_heap_101 output_ptrs output_words )
|--
  “ (((i - start ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((i - start ) + 1 )) ”
.

Definition words_string_safety_wit_21 := 
forall (input_ptr: Z) (input: (@list Z)) (start: Z) (data: Z) (out: Z) (cap: Z) (output_ptrs: (@list Z)) (output_words: (@list (@list Z))) (output_size: Z) (n: Z) (i: Z) (PreH1 : (start >= 0)) (PreH2 : ((Znth i (c_string (input)) 0) = 32)) (PreH3 : (i < n)) (PreH4 : (i <= n)) (PreH5 : (0 <= i)) (PreH6 : (i <= (n + 1 ))) (PreH7 : (n = (string_length (input)))) (PreH8 : (0 <= output_size)) (PreH9 : (output_size <= i)) (PreH10 : (output_size = (Zlength (output_words)))) (PreH11 : (output_size = (Zlength (output_ptrs)))) (PreH12 : (cap = (n + 1 ))) (PreH13 : (0 <= cap)) (PreH14 : (cap < INT_MAX)) (PreH15 : (output_size <= cap)) (PreH16 : (out <> 0)) (PreH17 : (data <> 0)) (PreH18 : (split_prefix_state_101 input i start output_words )) (PreH19 : (problem_101_pre_z input )) (PreH20 : (valid_string input )) (PreH21 : ((2 * ((string_length (input)) + 1 ) ) < INT_MAX)) ,
  ((( &( "w" ) )) # Ptr  |->_)
  **  ((( &( "len" ) )) # Int  |-> (i - start ))
  **  ((( &( "ch" ) )) # Char  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "s" ) )) # Ptr  |-> input_ptr)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (store_string input_ptr input )
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size cap )
  **  (words_rows_heap_101 output_ptrs output_words )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition words_string_safety_wit_22 := 
forall (input_ptr: Z) (input: (@list Z)) (start: Z) (data: Z) (out: Z) (cap: Z) (output_ptrs: (@list Z)) (output_words: (@list (@list Z))) (output_size: Z) (n: Z) (i: Z) (PreH1 : (start >= 0)) (PreH2 : ((Znth i (c_string (input)) 0) = 44)) (PreH3 : ((Znth i (c_string (input)) 0) <> 32)) (PreH4 : (i < n)) (PreH5 : (i <= n)) (PreH6 : (0 <= i)) (PreH7 : (i <= (n + 1 ))) (PreH8 : (n = (string_length (input)))) (PreH9 : (0 <= output_size)) (PreH10 : (output_size <= i)) (PreH11 : (output_size = (Zlength (output_words)))) (PreH12 : (output_size = (Zlength (output_ptrs)))) (PreH13 : (cap = (n + 1 ))) (PreH14 : (0 <= cap)) (PreH15 : (cap < INT_MAX)) (PreH16 : (output_size <= cap)) (PreH17 : (out <> 0)) (PreH18 : (data <> 0)) (PreH19 : (split_prefix_state_101 input i start output_words )) (PreH20 : (problem_101_pre_z input )) (PreH21 : (valid_string input )) (PreH22 : ((2 * ((string_length (input)) + 1 ) ) < INT_MAX)) ,
  ((( &( "w" ) )) # Ptr  |->_)
  **  ((( &( "len" ) )) # Int  |-> (i - start ))
  **  ((( &( "ch" ) )) # Char  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "s" ) )) # Ptr  |-> input_ptr)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (store_string input_ptr input )
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size cap )
  **  (words_rows_heap_101 output_ptrs output_words )
|--
  “ (((i - start ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((i - start ) + 1 )) ”
.

Definition words_string_safety_wit_23 := 
forall (input_ptr: Z) (input: (@list Z)) (start: Z) (data: Z) (out: Z) (cap: Z) (output_ptrs: (@list Z)) (output_words: (@list (@list Z))) (output_size: Z) (n: Z) (i: Z) (PreH1 : (start >= 0)) (PreH2 : ((Znth i (c_string (input)) 0) = 44)) (PreH3 : ((Znth i (c_string (input)) 0) <> 32)) (PreH4 : (i < n)) (PreH5 : (i <= n)) (PreH6 : (0 <= i)) (PreH7 : (i <= (n + 1 ))) (PreH8 : (n = (string_length (input)))) (PreH9 : (0 <= output_size)) (PreH10 : (output_size <= i)) (PreH11 : (output_size = (Zlength (output_words)))) (PreH12 : (output_size = (Zlength (output_ptrs)))) (PreH13 : (cap = (n + 1 ))) (PreH14 : (0 <= cap)) (PreH15 : (cap < INT_MAX)) (PreH16 : (output_size <= cap)) (PreH17 : (out <> 0)) (PreH18 : (data <> 0)) (PreH19 : (split_prefix_state_101 input i start output_words )) (PreH20 : (problem_101_pre_z input )) (PreH21 : (valid_string input )) (PreH22 : ((2 * ((string_length (input)) + 1 ) ) < INT_MAX)) ,
  ((( &( "w" ) )) # Ptr  |->_)
  **  ((( &( "len" ) )) # Int  |-> (i - start ))
  **  ((( &( "ch" ) )) # Char  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "s" ) )) # Ptr  |-> input_ptr)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (store_string input_ptr input )
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size cap )
  **  (words_rows_heap_101 output_ptrs output_words )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition words_string_safety_wit_24 := 
forall (input_ptr: Z) (input: (@list Z)) (input_pre: (@list Z)) (input_post: (@list Z)) (output_words: (@list (@list Z))) (output_ptrs: (@list Z)) (start: Z) (i: Z) (n: Z) (len: Z) (output_size: Z) (cap: Z) (out: Z) (data: Z) (w: Z) (ch: Z) (retval: Z) (PreH1 : (retval = w)) (PreH2 : (0 <= start)) (PreH3 : (start < i)) (PreH4 : (i <= n)) (PreH5 : (len = (i - start ))) (PreH6 : ((Zlength ((sublist (start) (i) (input)))) = len)) (PreH7 : (all_ascii (sublist (start) (i) (input)) )) (PreH8 : (input_pre = (sublist (0) (start) ((c_string (input)))))) (PreH9 : (input_post = (sublist (i) ((n + 1 )) ((c_string (input)))))) (PreH10 : (n = (string_length (input)))) (PreH11 : (0 <= output_size)) (PreH12 : (output_size <= i)) (PreH13 : (output_size = (Zlength (output_words)))) (PreH14 : (output_size = (Zlength (output_ptrs)))) (PreH15 : (output_size <= cap)) (PreH16 : (cap = (n + 1 ))) (PreH17 : (0 <= cap)) (PreH18 : (cap < INT_MAX)) (PreH19 : (out <> 0)) (PreH20 : (data <> 0)) (PreH21 : (w <> 0)) (PreH22 : (closing_delimiter_101 input i n )) (PreH23 : (split_prefix_state_101 input i start output_words )) (PreH24 : (problem_101_pre_z input )) (PreH25 : (valid_string input )) (PreH26 : ((2 * ((string_length (input)) + 1 ) ) < INT_MAX)) ,
  (CharArray.full w len (sublist (start) (i) (input)) )
  **  (CharArray.full (input_ptr + (start * sizeof(CHAR) ) ) len (sublist (start) (i) (input)) )
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "ch" ) )) # Char  |-> ch)
  **  ((( &( "s" ) )) # Ptr  |-> input_ptr)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (CharArray.seg input_ptr 0 start input_pre )
  **  (CharArray.seg input_ptr i (n + 1 ) input_post )
  **  (CharArray.undef_seg w len (len + 1 ) )
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size cap )
  **  (words_rows_heap_101 output_ptrs output_words )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition words_string_safety_wit_25 := 
forall (input_ptr: Z) (input: (@list Z)) (output_words: (@list (@list Z))) (output_ptrs: (@list Z)) (start: Z) (i: Z) (n: Z) (len: Z) (output_size: Z) (cap: Z) (out: Z) (data: Z) (w: Z) (ch: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (0 <= (Zlength ((c_string ((sublist (start) (i) (input)))))))) (PreH3 : (0 <= start)) (PreH4 : (start < i)) (PreH5 : (i <= n)) (PreH6 : (len = (i - start ))) (PreH7 : (n = (string_length (input)))) (PreH8 : (0 <= output_size)) (PreH9 : (output_size <= i)) (PreH10 : (output_size = (Zlength (output_words)))) (PreH11 : (output_size = (Zlength (output_ptrs)))) (PreH12 : (output_size < cap)) (PreH13 : (cap = (n + 1 ))) (PreH14 : (0 <= cap)) (PreH15 : (cap < INT_MAX)) (PreH16 : (out <> 0)) (PreH17 : (data <> 0)) (PreH18 : (w <> 0)) (PreH19 : (closing_delimiter_101 input i n )) (PreH20 : (split_prefix_state_101 input i start output_words )) (PreH21 : (problem_101_pre_z input )) (PreH22 : (valid_string input )) (PreH23 : ((2 * ((string_length (input)) + 1 ) ) < INT_MAX)) ,
  (PtrArray.seg data 0 (output_size + 1 ) (app (output_ptrs) ((cons (w) ((@nil Z))))) )
  **  (PtrArray.undef_seg data (output_size + 1 ) cap )
  **  (CharArray.full input_ptr ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "ch" ) )) # Char  |-> ch)
  **  ((( &( "s" ) )) # Ptr  |-> input_ptr)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (CharArray.full w (Zlength ((c_string ((sublist (start) (i) (input)))))) (c_string ((sublist (start) (i) (input)))) )
  **  (words_rows_heap_101 output_ptrs output_words )
|--
  “ ((output_size + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (output_size + 1 )) ”
.

Definition words_string_safety_wit_26 := 
forall (input_ptr: Z) (input: (@list Z)) (output_words: (@list (@list Z))) (output_ptrs: (@list Z)) (start: Z) (i: Z) (n: Z) (len: Z) (output_size: Z) (cap: Z) (out: Z) (data: Z) (w: Z) (ch: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (0 <= (Zlength ((c_string ((sublist (start) (i) (input)))))))) (PreH3 : (0 <= start)) (PreH4 : (start < i)) (PreH5 : (i <= n)) (PreH6 : (len = (i - start ))) (PreH7 : (n = (string_length (input)))) (PreH8 : (0 <= output_size)) (PreH9 : (output_size <= i)) (PreH10 : (output_size = (Zlength (output_words)))) (PreH11 : (output_size = (Zlength (output_ptrs)))) (PreH12 : (output_size < cap)) (PreH13 : (cap = (n + 1 ))) (PreH14 : (0 <= cap)) (PreH15 : (cap < INT_MAX)) (PreH16 : (out <> 0)) (PreH17 : (data <> 0)) (PreH18 : (w <> 0)) (PreH19 : (closing_delimiter_101 input i n )) (PreH20 : (split_prefix_state_101 input i start output_words )) (PreH21 : (problem_101_pre_z input )) (PreH22 : (valid_string input )) (PreH23 : ((2 * ((string_length (input)) + 1 ) ) < INT_MAX)) ,
  (PtrArray.seg data 0 (output_size + 1 ) (app (output_ptrs) ((cons (w) ((@nil Z))))) )
  **  (PtrArray.undef_seg data (output_size + 1 ) cap )
  **  (CharArray.full input_ptr ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "output_size" ) )) # Int  |-> (output_size + 1 ))
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "ch" ) )) # Char  |-> ch)
  **  ((( &( "s" ) )) # Ptr  |-> input_ptr)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (output_size + 1 ))
  **  (CharArray.full w (Zlength ((c_string ((sublist (start) (i) (input)))))) (c_string ((sublist (start) (i) (input)))) )
  **  (words_rows_heap_101 output_ptrs output_words )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition words_string_safety_wit_27 := 
forall (input_ptr: Z) (input: (@list Z)) (output_words: (@list (@list Z))) (output_ptrs: (@list Z)) (start: Z) (i: Z) (n: Z) (len: Z) (output_size: Z) (cap: Z) (out: Z) (data: Z) (w: Z) (ch: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (0 <= (Zlength ((c_string ((sublist (start) (i) (input)))))))) (PreH3 : (0 <= start)) (PreH4 : (start < i)) (PreH5 : (i <= n)) (PreH6 : (len = (i - start ))) (PreH7 : (n = (string_length (input)))) (PreH8 : (0 <= output_size)) (PreH9 : (output_size <= i)) (PreH10 : (output_size = (Zlength (output_words)))) (PreH11 : (output_size = (Zlength (output_ptrs)))) (PreH12 : (output_size < cap)) (PreH13 : (cap = (n + 1 ))) (PreH14 : (0 <= cap)) (PreH15 : (cap < INT_MAX)) (PreH16 : (out <> 0)) (PreH17 : (data <> 0)) (PreH18 : (w <> 0)) (PreH19 : (closing_delimiter_101 input i n )) (PreH20 : (split_prefix_state_101 input i start output_words )) (PreH21 : (problem_101_pre_z input )) (PreH22 : (valid_string input )) (PreH23 : ((2 * ((string_length (input)) + 1 ) ) < INT_MAX)) ,
  (PtrArray.seg data 0 (output_size + 1 ) (app (output_ptrs) ((cons (w) ((@nil Z))))) )
  **  (PtrArray.undef_seg data (output_size + 1 ) cap )
  **  (CharArray.full input_ptr ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "output_size" ) )) # Int  |-> (output_size + 1 ))
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "ch" ) )) # Char  |-> ch)
  **  ((( &( "s" ) )) # Ptr  |-> input_ptr)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (output_size + 1 ))
  **  (CharArray.full w (Zlength ((c_string ((sublist (start) (i) (input)))))) (c_string ((sublist (start) (i) (input)))) )
  **  (words_rows_heap_101 output_ptrs output_words )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition words_string_safety_wit_28 := 
forall (input_ptr: Z) (input: (@list Z)) (start: Z) (data: Z) (out: Z) (cap: Z) (output_ptrs: (@list Z)) (output_words: (@list (@list Z))) (output_size: Z) (n: Z) (i: Z) (PreH1 : ((Znth i (c_string (input)) 0) <> 44)) (PreH2 : ((Znth i (c_string (input)) 0) <> 32)) (PreH3 : (i < n)) (PreH4 : (i <= n)) (PreH5 : (0 <= i)) (PreH6 : (i <= (n + 1 ))) (PreH7 : (n = (string_length (input)))) (PreH8 : (0 <= output_size)) (PreH9 : (output_size <= i)) (PreH10 : (output_size = (Zlength (output_words)))) (PreH11 : (output_size = (Zlength (output_ptrs)))) (PreH12 : (cap = (n + 1 ))) (PreH13 : (0 <= cap)) (PreH14 : (cap < INT_MAX)) (PreH15 : (output_size <= cap)) (PreH16 : (out <> 0)) (PreH17 : (data <> 0)) (PreH18 : (split_prefix_state_101 input i start output_words )) (PreH19 : (problem_101_pre_z input )) (PreH20 : (valid_string input )) (PreH21 : ((2 * ((string_length (input)) + 1 ) ) < INT_MAX)) ,
  ((( &( "ch" ) )) # Char  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "s" ) )) # Ptr  |-> input_ptr)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (store_string input_ptr input )
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size cap )
  **  (words_rows_heap_101 output_ptrs output_words )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition words_string_safety_wit_29 := 
forall (input_ptr: Z) (input: (@list Z)) (output_words: (@list (@list Z))) (output_ptrs: (@list Z)) (start: Z) (i: Z) (n: Z) (len: Z) (output_size: Z) (cap: Z) (out: Z) (data: Z) (w: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (0 <= (Zlength ((c_string ((sublist (start) (i) (input)))))))) (PreH3 : (0 <= start)) (PreH4 : (start < i)) (PreH5 : (i <= n)) (PreH6 : (len = (i - start ))) (PreH7 : (n = (string_length (input)))) (PreH8 : (0 <= output_size)) (PreH9 : (output_size <= i)) (PreH10 : (output_size = (Zlength (output_words)))) (PreH11 : (output_size = (Zlength (output_ptrs)))) (PreH12 : (output_size < cap)) (PreH13 : (cap = (n + 1 ))) (PreH14 : (0 <= cap)) (PreH15 : (cap < INT_MAX)) (PreH16 : (out <> 0)) (PreH17 : (data <> 0)) (PreH18 : (w <> 0)) (PreH19 : (closing_delimiter_101 input i n )) (PreH20 : (split_prefix_state_101 input i start output_words )) (PreH21 : (problem_101_pre_z input )) (PreH22 : (valid_string input )) (PreH23 : ((2 * ((string_length (input)) + 1 ) ) < INT_MAX)) ,
  (PtrArray.seg data 0 (output_size + 1 ) (app (output_ptrs) ((cons (w) ((@nil Z))))) )
  **  (PtrArray.undef_seg data (output_size + 1 ) cap )
  **  (CharArray.full input_ptr ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "start" ) )) # Int  |-> (-1))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "output_size" ) )) # Int  |-> (output_size + 1 ))
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "s" ) )) # Ptr  |-> input_ptr)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (output_size + 1 ))
  **  (CharArray.full w (Zlength ((c_string ((sublist (start) (i) (input)))))) (c_string ((sublist (start) (i) (input)))) )
  **  (words_rows_heap_101 output_ptrs output_words )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition words_string_safety_wit_30 := 
forall (input_ptr: Z) (input: (@list Z)) (start: Z) (data: Z) (out: Z) (cap: Z) (output_ptrs: (@list Z)) (output_words: (@list (@list Z))) (output_size: Z) (n: Z) (i: Z) (PreH1 : (start < 0)) (PreH2 : (i >= n)) (PreH3 : (i <= n)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n + 1 ))) (PreH6 : (n = (string_length (input)))) (PreH7 : (0 <= output_size)) (PreH8 : (output_size <= i)) (PreH9 : (output_size = (Zlength (output_words)))) (PreH10 : (output_size = (Zlength (output_ptrs)))) (PreH11 : (cap = (n + 1 ))) (PreH12 : (0 <= cap)) (PreH13 : (cap < INT_MAX)) (PreH14 : (output_size <= cap)) (PreH15 : (out <> 0)) (PreH16 : (data <> 0)) (PreH17 : (split_prefix_state_101 input i start output_words )) (PreH18 : (problem_101_pre_z input )) (PreH19 : (valid_string input )) (PreH20 : ((2 * ((string_length (input)) + 1 ) ) < INT_MAX)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "s" ) )) # Ptr  |-> input_ptr)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (store_string input_ptr input )
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size cap )
  **  (words_rows_heap_101 output_ptrs output_words )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition words_string_safety_wit_31 := 
forall (input_ptr: Z) (input: (@list Z)) (start: Z) (data: Z) (out: Z) (cap: Z) (output_ptrs: (@list Z)) (output_words: (@list (@list Z))) (output_size: Z) (n: Z) (i: Z) (PreH1 : (start < 0)) (PreH2 : ((Znth i (c_string (input)) 0) = 32)) (PreH3 : (i < n)) (PreH4 : (i <= n)) (PreH5 : (0 <= i)) (PreH6 : (i <= (n + 1 ))) (PreH7 : (n = (string_length (input)))) (PreH8 : (0 <= output_size)) (PreH9 : (output_size <= i)) (PreH10 : (output_size = (Zlength (output_words)))) (PreH11 : (output_size = (Zlength (output_ptrs)))) (PreH12 : (cap = (n + 1 ))) (PreH13 : (0 <= cap)) (PreH14 : (cap < INT_MAX)) (PreH15 : (output_size <= cap)) (PreH16 : (out <> 0)) (PreH17 : (data <> 0)) (PreH18 : (split_prefix_state_101 input i start output_words )) (PreH19 : (problem_101_pre_z input )) (PreH20 : (valid_string input )) (PreH21 : ((2 * ((string_length (input)) + 1 ) ) < INT_MAX)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "s" ) )) # Ptr  |-> input_ptr)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (store_string input_ptr input )
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size cap )
  **  (words_rows_heap_101 output_ptrs output_words )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition words_string_safety_wit_32 := 
forall (input_ptr: Z) (input: (@list Z)) (start: Z) (data: Z) (out: Z) (cap: Z) (output_ptrs: (@list Z)) (output_words: (@list (@list Z))) (output_size: Z) (n: Z) (i: Z) (PreH1 : (start < 0)) (PreH2 : ((Znth i (c_string (input)) 0) = 44)) (PreH3 : ((Znth i (c_string (input)) 0) <> 32)) (PreH4 : (i < n)) (PreH5 : (i <= n)) (PreH6 : (0 <= i)) (PreH7 : (i <= (n + 1 ))) (PreH8 : (n = (string_length (input)))) (PreH9 : (0 <= output_size)) (PreH10 : (output_size <= i)) (PreH11 : (output_size = (Zlength (output_words)))) (PreH12 : (output_size = (Zlength (output_ptrs)))) (PreH13 : (cap = (n + 1 ))) (PreH14 : (0 <= cap)) (PreH15 : (cap < INT_MAX)) (PreH16 : (output_size <= cap)) (PreH17 : (out <> 0)) (PreH18 : (data <> 0)) (PreH19 : (split_prefix_state_101 input i start output_words )) (PreH20 : (problem_101_pre_z input )) (PreH21 : (valid_string input )) (PreH22 : ((2 * ((string_length (input)) + 1 ) ) < INT_MAX)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "s" ) )) # Ptr  |-> input_ptr)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (store_string input_ptr input )
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size cap )
  **  (words_rows_heap_101 output_ptrs output_words )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition words_string_safety_wit_33 := 
forall (input_ptr: Z) (input: (@list Z)) (start: Z) (data: Z) (out: Z) (cap: Z) (output_ptrs: (@list Z)) (output_words: (@list (@list Z))) (output_size: Z) (n: Z) (i: Z) (PreH1 : (start < 0)) (PreH2 : ((Znth i (c_string (input)) 0) <> 44)) (PreH3 : ((Znth i (c_string (input)) 0) <> 32)) (PreH4 : (i < n)) (PreH5 : (i <= n)) (PreH6 : (0 <= i)) (PreH7 : (i <= (n + 1 ))) (PreH8 : (n = (string_length (input)))) (PreH9 : (0 <= output_size)) (PreH10 : (output_size <= i)) (PreH11 : (output_size = (Zlength (output_words)))) (PreH12 : (output_size = (Zlength (output_ptrs)))) (PreH13 : (cap = (n + 1 ))) (PreH14 : (0 <= cap)) (PreH15 : (cap < INT_MAX)) (PreH16 : (output_size <= cap)) (PreH17 : (out <> 0)) (PreH18 : (data <> 0)) (PreH19 : (split_prefix_state_101 input i start output_words )) (PreH20 : (problem_101_pre_z input )) (PreH21 : (valid_string input )) (PreH22 : ((2 * ((string_length (input)) + 1 ) ) < INT_MAX)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "s" ) )) # Ptr  |-> input_ptr)
  **  ((( &( "start" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (store_string input_ptr input )
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size cap )
  **  (words_rows_heap_101 output_ptrs output_words )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition words_string_safety_wit_34 := 
forall (input_ptr: Z) (input: (@list Z)) (start: Z) (data: Z) (out: Z) (cap: Z) (output_ptrs: (@list Z)) (output_words: (@list (@list Z))) (output_size: Z) (n: Z) (i: Z) (PreH1 : (start >= 0)) (PreH2 : ((Znth i (c_string (input)) 0) <> 44)) (PreH3 : ((Znth i (c_string (input)) 0) <> 32)) (PreH4 : (i < n)) (PreH5 : (i <= n)) (PreH6 : (0 <= i)) (PreH7 : (i <= (n + 1 ))) (PreH8 : (n = (string_length (input)))) (PreH9 : (0 <= output_size)) (PreH10 : (output_size <= i)) (PreH11 : (output_size = (Zlength (output_words)))) (PreH12 : (output_size = (Zlength (output_ptrs)))) (PreH13 : (cap = (n + 1 ))) (PreH14 : (0 <= cap)) (PreH15 : (cap < INT_MAX)) (PreH16 : (output_size <= cap)) (PreH17 : (out <> 0)) (PreH18 : (data <> 0)) (PreH19 : (split_prefix_state_101 input i start output_words )) (PreH20 : (problem_101_pre_z input )) (PreH21 : (valid_string input )) (PreH22 : ((2 * ((string_length (input)) + 1 ) ) < INT_MAX)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "s" ) )) # Ptr  |-> input_ptr)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (store_string input_ptr input )
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size cap )
  **  (words_rows_heap_101 output_ptrs output_words )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition words_string_entail_wit_1 := 
(
forall (s_pre: Z) (input_ptr: Z) (input: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 = (string_length (input)))) (PreH3 : (retval <> 0)) (PreH4 : (0 <= ((string_length (input)) + 1 ))) (PreH5 : (s_pre = input_ptr)) (PreH6 : (problem_101_pre_z input )) (PreH7 : (valid_string input )) (PreH8 : ((2 * ((string_length (input)) + 1 ) ) < INT_MAX)) ,
  (PtrArray.undef_seg retval_3 0 (retval_2 + 1 ) )
  **  (CharArray.full s_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_3)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  EX (output_ptrs: (@list Z))  (output_words: (@list (@list Z))) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= (retval_2 + 1 )) ” 
  &&  “ (retval_2 = (string_length (input))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 = (Zlength (output_words))) ” 
  &&  “ (0 = (Zlength (output_ptrs))) ” 
  &&  “ ((retval_2 + 1 ) = (retval_2 + 1 )) ” 
  &&  “ (0 <= (retval_2 + 1 )) ” 
  &&  “ ((retval_2 + 1 ) < INT_MAX) ” 
  &&  “ (0 <= (retval_2 + 1 )) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval_3 <> 0) ” 
  &&  “ (split_prefix_state_101 input 0 (-1) output_words ) ” 
  &&  “ (problem_101_pre_z input ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ ((2 * ((string_length (input)) + 1 ) ) < INT_MAX) ”
  &&  ((( &( "s" ) )) # Ptr  |-> input_ptr)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_3)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (store_string input_ptr input )
  **  (PtrArray.seg retval_3 0 0 output_ptrs )
  **  (PtrArray.undef_seg retval_3 0 (retval_2 + 1 ) )
  **  (words_rows_heap_101 output_ptrs output_words )
) \/
(
forall (s_pre: Z) (input_ptr: Z) (input: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 = (string_length (input)))) (PreH3 : (retval <> 0)) (PreH4 : (0 <= ((string_length (input)) + 1 ))) (PreH5 : (s_pre = input_ptr)) (PreH6 : (problem_101_pre_z input )) (PreH7 : (valid_string input )) (PreH8 : ((2 * ((string_length (input)) + 1 ) ) < INT_MAX)) ,
  (CharArray.full s_pre ((string_length (input)) + 1 ) (c_string (input)) )
|--
  EX (output_words: (@list (@list Z))) ,
  “ (s_pre = input_ptr) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (retval_2 + 1 )) ” 
  &&  “ (retval_2 = (string_length (input))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 = (Zlength (output_words))) ” 
  &&  “ (0 = (Zlength ((@nil Z)))) ” 
  &&  “ (0 <= (retval_2 + 1 )) ” 
  &&  “ ((retval_2 + 1 ) < INT_MAX) ” 
  &&  “ (0 <= (retval_2 + 1 )) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval_3 <> 0) ” 
  &&  “ (split_prefix_state_101 input 0 (-1) output_words ) ” 
  &&  “ (problem_101_pre_z input ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ ((2 * ((string_length (input)) + 1 ) ) < INT_MAX) ”
  &&  (CharArray.full input_ptr ((string_length (input)) + 1 ) (c_string (input)) )
  **  (words_rows_heap_101 (@nil Z) output_words )
).

Definition words_string_entail_wit_2_1 := 
(
forall (input_ptr: Z) (input: (@list Z)) (start: Z) (data: Z) (out: Z) (cap: Z) (output_ptrs_2: (@list Z)) (output_words_2: (@list (@list Z))) (output_size: Z) (n: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (start >= 0)) (PreH4 : ((Znth i (c_string (input)) 0) = 44)) (PreH5 : ((Znth i (c_string (input)) 0) <> 32)) (PreH6 : (i < n)) (PreH7 : (i <= n)) (PreH8 : (0 <= i)) (PreH9 : (i <= (n + 1 ))) (PreH10 : (n = (string_length (input)))) (PreH11 : (0 <= output_size)) (PreH12 : (output_size <= i)) (PreH13 : (output_size = (Zlength (output_words_2)))) (PreH14 : (output_size = (Zlength (output_ptrs_2)))) (PreH15 : (cap = (n + 1 ))) (PreH16 : (0 <= cap)) (PreH17 : (cap < INT_MAX)) (PreH18 : (output_size <= cap)) (PreH19 : (out <> 0)) (PreH20 : (data <> 0)) (PreH21 : (split_prefix_state_101 input i start output_words_2 )) (PreH22 : (problem_101_pre_z input )) (PreH23 : (valid_string input )) (PreH24 : ((2 * ((string_length (input)) + 1 ) ) < INT_MAX)) ,
  (CharArray.undef_full retval ((i - start ) + 1 ) )
  **  (CharArray.full input_ptr ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (PtrArray.seg data 0 output_size output_ptrs_2 )
  **  (PtrArray.undef_seg data output_size cap )
  **  (words_rows_heap_101 output_ptrs_2 output_words_2 )
|--
  EX (output_ptrs: (@list Z))  (output_words: (@list (@list Z)))  (input_post: (@list Z))  (input_pre: (@list Z)) ,
  “ (0 <= start) ” 
  &&  “ (start < i) ” 
  &&  “ (i <= n) ” 
  &&  “ ((i - start ) = (i - start )) ” 
  &&  “ ((Zlength ((sublist (start) (i) (input)))) = (i - start )) ” 
  &&  “ (all_ascii (sublist (start) (i) (input)) ) ” 
  &&  “ (input_pre = (sublist (0) (start) ((c_string (input))))) ” 
  &&  “ (input_post = (sublist (i) ((n + 1 )) ((c_string (input))))) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= i) ” 
  &&  “ (output_size = (Zlength (output_words))) ” 
  &&  “ (output_size = (Zlength (output_ptrs))) ” 
  &&  “ (output_size <= cap) ” 
  &&  “ (cap = (n + 1 )) ” 
  &&  “ (0 <= cap) ” 
  &&  “ (cap < INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (closing_delimiter_101 input i n ) ” 
  &&  “ (split_prefix_state_101 input i start output_words ) ” 
  &&  “ (problem_101_pre_z input ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ ((2 * ((string_length (input)) + 1 ) ) < INT_MAX) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (CharArray.seg input_ptr 0 start input_pre )
  **  (CharArray.full (input_ptr + (start * sizeof(CHAR) ) ) (i - start ) (sublist (start) (i) (input)) )
  **  (CharArray.seg input_ptr i (n + 1 ) input_post )
  **  (CharArray.undef_full retval (i - start ) )
  **  (CharArray.undef_seg retval (i - start ) ((i - start ) + 1 ) )
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size cap )
  **  (words_rows_heap_101 output_ptrs output_words )
) \/
(
forall (input_ptr: Z) (input: (@list Z)) (start: Z) (data: Z) (out: Z) (cap: Z) (output_ptrs_2: (@list Z)) (output_words_2: (@list (@list Z))) (output_size: Z) (n: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (start >= 0)) (PreH4 : ((Znth i (c_string (input)) 0) = 44)) (PreH5 : ((Znth i (c_string (input)) 0) <> 32)) (PreH6 : (i < n)) (PreH7 : (i <= n)) (PreH8 : (0 <= i)) (PreH9 : (i <= (n + 1 ))) (PreH10 : (n = (string_length (input)))) (PreH11 : (0 <= output_size)) (PreH12 : (output_size <= i)) (PreH13 : (output_size = (Zlength (output_words_2)))) (PreH14 : (output_size = (Zlength (output_ptrs_2)))) (PreH15 : (cap = (n + 1 ))) (PreH16 : (0 <= cap)) (PreH17 : (cap < INT_MAX)) (PreH18 : (output_size <= cap)) (PreH19 : (out <> 0)) (PreH20 : (data <> 0)) (PreH21 : (split_prefix_state_101 input i start output_words_2 )) (PreH22 : (problem_101_pre_z input )) (PreH23 : (valid_string input )) (PreH24 : ((2 * ((string_length (input)) + 1 ) ) < INT_MAX)) ,
  (CharArray.undef_full retval ((i - start ) + 1 ) )
  **  (CharArray.full input_ptr ((string_length (input)) + 1 ) (c_string (input)) )
  **  (words_rows_heap_101 output_ptrs_2 output_words_2 )
|--
  EX (output_words: (@list (@list Z))) ,
  “ (0 <= start) ” 
  &&  “ (start < i) ” 
  &&  “ (i <= n) ” 
  &&  “ ((Zlength ((sublist (start) (i) (input)))) = (i - start )) ” 
  &&  “ (all_ascii (sublist (start) (i) (input)) ) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= i) ” 
  &&  “ (output_size = (Zlength (output_words))) ” 
  &&  “ (output_size = (Zlength (output_ptrs_2))) ” 
  &&  “ (output_size <= cap) ” 
  &&  “ (cap = (n + 1 )) ” 
  &&  “ (0 <= cap) ” 
  &&  “ (cap < INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (closing_delimiter_101 input i n ) ” 
  &&  “ (split_prefix_state_101 input i start output_words ) ” 
  &&  “ (problem_101_pre_z input ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ ((2 * ((string_length (input)) + 1 ) ) < INT_MAX) ”
  &&  (CharArray.seg input_ptr 0 start (sublist (0) (start) ((c_string (input)))) )
  **  (CharArray.full (input_ptr + (start * sizeof(CHAR) ) ) (i - start ) (sublist (start) (i) (input)) )
  **  (CharArray.seg input_ptr i (n + 1 ) (sublist (i) ((n + 1 )) ((c_string (input)))) )
  **  (CharArray.undef_full retval (i - start ) )
  **  (CharArray.undef_seg retval (i - start ) ((i - start ) + 1 ) )
  **  (words_rows_heap_101 output_ptrs_2 output_words )
).

Definition words_string_entail_wit_2_2 := 
(
forall (input_ptr: Z) (input: (@list Z)) (start: Z) (data: Z) (out: Z) (cap: Z) (output_ptrs_2: (@list Z)) (output_words_2: (@list (@list Z))) (output_size: Z) (n: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (start >= 0)) (PreH4 : ((Znth i (c_string (input)) 0) = 32)) (PreH5 : (i < n)) (PreH6 : (i <= n)) (PreH7 : (0 <= i)) (PreH8 : (i <= (n + 1 ))) (PreH9 : (n = (string_length (input)))) (PreH10 : (0 <= output_size)) (PreH11 : (output_size <= i)) (PreH12 : (output_size = (Zlength (output_words_2)))) (PreH13 : (output_size = (Zlength (output_ptrs_2)))) (PreH14 : (cap = (n + 1 ))) (PreH15 : (0 <= cap)) (PreH16 : (cap < INT_MAX)) (PreH17 : (output_size <= cap)) (PreH18 : (out <> 0)) (PreH19 : (data <> 0)) (PreH20 : (split_prefix_state_101 input i start output_words_2 )) (PreH21 : (problem_101_pre_z input )) (PreH22 : (valid_string input )) (PreH23 : ((2 * ((string_length (input)) + 1 ) ) < INT_MAX)) ,
  (CharArray.undef_full retval ((i - start ) + 1 ) )
  **  (CharArray.full input_ptr ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (PtrArray.seg data 0 output_size output_ptrs_2 )
  **  (PtrArray.undef_seg data output_size cap )
  **  (words_rows_heap_101 output_ptrs_2 output_words_2 )
|--
  EX (output_ptrs: (@list Z))  (output_words: (@list (@list Z)))  (input_post: (@list Z))  (input_pre: (@list Z)) ,
  “ (0 <= start) ” 
  &&  “ (start < i) ” 
  &&  “ (i <= n) ” 
  &&  “ ((i - start ) = (i - start )) ” 
  &&  “ ((Zlength ((sublist (start) (i) (input)))) = (i - start )) ” 
  &&  “ (all_ascii (sublist (start) (i) (input)) ) ” 
  &&  “ (input_pre = (sublist (0) (start) ((c_string (input))))) ” 
  &&  “ (input_post = (sublist (i) ((n + 1 )) ((c_string (input))))) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= i) ” 
  &&  “ (output_size = (Zlength (output_words))) ” 
  &&  “ (output_size = (Zlength (output_ptrs))) ” 
  &&  “ (output_size <= cap) ” 
  &&  “ (cap = (n + 1 )) ” 
  &&  “ (0 <= cap) ” 
  &&  “ (cap < INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (closing_delimiter_101 input i n ) ” 
  &&  “ (split_prefix_state_101 input i start output_words ) ” 
  &&  “ (problem_101_pre_z input ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ ((2 * ((string_length (input)) + 1 ) ) < INT_MAX) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (CharArray.seg input_ptr 0 start input_pre )
  **  (CharArray.full (input_ptr + (start * sizeof(CHAR) ) ) (i - start ) (sublist (start) (i) (input)) )
  **  (CharArray.seg input_ptr i (n + 1 ) input_post )
  **  (CharArray.undef_full retval (i - start ) )
  **  (CharArray.undef_seg retval (i - start ) ((i - start ) + 1 ) )
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size cap )
  **  (words_rows_heap_101 output_ptrs output_words )
) \/
(
forall (input_ptr: Z) (input: (@list Z)) (start: Z) (data: Z) (out: Z) (cap: Z) (output_ptrs_2: (@list Z)) (output_words_2: (@list (@list Z))) (output_size: Z) (n: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (start >= 0)) (PreH4 : ((Znth i (c_string (input)) 0) = 32)) (PreH5 : (i < n)) (PreH6 : (i <= n)) (PreH7 : (0 <= i)) (PreH8 : (i <= (n + 1 ))) (PreH9 : (n = (string_length (input)))) (PreH10 : (0 <= output_size)) (PreH11 : (output_size <= i)) (PreH12 : (output_size = (Zlength (output_words_2)))) (PreH13 : (output_size = (Zlength (output_ptrs_2)))) (PreH14 : (cap = (n + 1 ))) (PreH15 : (0 <= cap)) (PreH16 : (cap < INT_MAX)) (PreH17 : (output_size <= cap)) (PreH18 : (out <> 0)) (PreH19 : (data <> 0)) (PreH20 : (split_prefix_state_101 input i start output_words_2 )) (PreH21 : (problem_101_pre_z input )) (PreH22 : (valid_string input )) (PreH23 : ((2 * ((string_length (input)) + 1 ) ) < INT_MAX)) ,
  (CharArray.undef_full retval ((i - start ) + 1 ) )
  **  (CharArray.full input_ptr ((string_length (input)) + 1 ) (c_string (input)) )
  **  (words_rows_heap_101 output_ptrs_2 output_words_2 )
|--
  EX (output_words: (@list (@list Z))) ,
  “ (0 <= start) ” 
  &&  “ (start < i) ” 
  &&  “ (i <= n) ” 
  &&  “ ((Zlength ((sublist (start) (i) (input)))) = (i - start )) ” 
  &&  “ (all_ascii (sublist (start) (i) (input)) ) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= i) ” 
  &&  “ (output_size = (Zlength (output_words))) ” 
  &&  “ (output_size = (Zlength (output_ptrs_2))) ” 
  &&  “ (output_size <= cap) ” 
  &&  “ (cap = (n + 1 )) ” 
  &&  “ (0 <= cap) ” 
  &&  “ (cap < INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (closing_delimiter_101 input i n ) ” 
  &&  “ (split_prefix_state_101 input i start output_words ) ” 
  &&  “ (problem_101_pre_z input ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ ((2 * ((string_length (input)) + 1 ) ) < INT_MAX) ”
  &&  (CharArray.seg input_ptr 0 start (sublist (0) (start) ((c_string (input)))) )
  **  (CharArray.full (input_ptr + (start * sizeof(CHAR) ) ) (i - start ) (sublist (start) (i) (input)) )
  **  (CharArray.seg input_ptr i (n + 1 ) (sublist (i) ((n + 1 )) ((c_string (input)))) )
  **  (CharArray.undef_full retval (i - start ) )
  **  (CharArray.undef_seg retval (i - start ) ((i - start ) + 1 ) )
  **  (words_rows_heap_101 output_ptrs_2 output_words )
).

Definition words_string_entail_wit_2_3 := 
(
forall (input_ptr: Z) (input: (@list Z)) (start: Z) (data: Z) (out: Z) (cap: Z) (output_ptrs_2: (@list Z)) (output_words_2: (@list (@list Z))) (output_size: Z) (n: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (start >= 0)) (PreH4 : (i >= n)) (PreH5 : (i <= n)) (PreH6 : (0 <= i)) (PreH7 : (i <= (n + 1 ))) (PreH8 : (n = (string_length (input)))) (PreH9 : (0 <= output_size)) (PreH10 : (output_size <= i)) (PreH11 : (output_size = (Zlength (output_words_2)))) (PreH12 : (output_size = (Zlength (output_ptrs_2)))) (PreH13 : (cap = (n + 1 ))) (PreH14 : (0 <= cap)) (PreH15 : (cap < INT_MAX)) (PreH16 : (output_size <= cap)) (PreH17 : (out <> 0)) (PreH18 : (data <> 0)) (PreH19 : (split_prefix_state_101 input i start output_words_2 )) (PreH20 : (problem_101_pre_z input )) (PreH21 : (valid_string input )) (PreH22 : ((2 * ((string_length (input)) + 1 ) ) < INT_MAX)) ,
  (CharArray.undef_full retval ((i - start ) + 1 ) )
  **  (CharArray.full input_ptr ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (PtrArray.seg data 0 output_size output_ptrs_2 )
  **  (PtrArray.undef_seg data output_size cap )
  **  (words_rows_heap_101 output_ptrs_2 output_words_2 )
|--
  EX (output_ptrs: (@list Z))  (output_words: (@list (@list Z)))  (input_post: (@list Z))  (input_pre: (@list Z)) ,
  “ (0 <= start) ” 
  &&  “ (start < i) ” 
  &&  “ (i <= n) ” 
  &&  “ ((i - start ) = (i - start )) ” 
  &&  “ ((Zlength ((sublist (start) (i) (input)))) = (i - start )) ” 
  &&  “ (all_ascii (sublist (start) (i) (input)) ) ” 
  &&  “ (input_pre = (sublist (0) (start) ((c_string (input))))) ” 
  &&  “ (input_post = (sublist (i) ((n + 1 )) ((c_string (input))))) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= i) ” 
  &&  “ (output_size = (Zlength (output_words))) ” 
  &&  “ (output_size = (Zlength (output_ptrs))) ” 
  &&  “ (output_size <= cap) ” 
  &&  “ (cap = (n + 1 )) ” 
  &&  “ (0 <= cap) ” 
  &&  “ (cap < INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (closing_delimiter_101 input i n ) ” 
  &&  “ (split_prefix_state_101 input i start output_words ) ” 
  &&  “ (problem_101_pre_z input ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ ((2 * ((string_length (input)) + 1 ) ) < INT_MAX) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (CharArray.seg input_ptr 0 start input_pre )
  **  (CharArray.full (input_ptr + (start * sizeof(CHAR) ) ) (i - start ) (sublist (start) (i) (input)) )
  **  (CharArray.seg input_ptr i (n + 1 ) input_post )
  **  (CharArray.undef_full retval (i - start ) )
  **  (CharArray.undef_seg retval (i - start ) ((i - start ) + 1 ) )
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size cap )
  **  (words_rows_heap_101 output_ptrs output_words )
) \/
(
forall (input_ptr: Z) (input: (@list Z)) (start: Z) (data: Z) (out: Z) (cap: Z) (output_ptrs_2: (@list Z)) (output_words_2: (@list (@list Z))) (output_size: Z) (n: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (start >= 0)) (PreH4 : (i >= n)) (PreH5 : (i <= n)) (PreH6 : (0 <= i)) (PreH7 : (i <= (n + 1 ))) (PreH8 : (n = (string_length (input)))) (PreH9 : (0 <= output_size)) (PreH10 : (output_size <= i)) (PreH11 : (output_size = (Zlength (output_words_2)))) (PreH12 : (output_size = (Zlength (output_ptrs_2)))) (PreH13 : (cap = (n + 1 ))) (PreH14 : (0 <= cap)) (PreH15 : (cap < INT_MAX)) (PreH16 : (output_size <= cap)) (PreH17 : (out <> 0)) (PreH18 : (data <> 0)) (PreH19 : (split_prefix_state_101 input i start output_words_2 )) (PreH20 : (problem_101_pre_z input )) (PreH21 : (valid_string input )) (PreH22 : ((2 * ((string_length (input)) + 1 ) ) < INT_MAX)) ,
  (CharArray.undef_full retval ((i - start ) + 1 ) )
  **  (CharArray.full input_ptr ((string_length (input)) + 1 ) (c_string (input)) )
  **  (words_rows_heap_101 output_ptrs_2 output_words_2 )
|--
  EX (output_words: (@list (@list Z))) ,
  “ (0 <= start) ” 
  &&  “ (start < i) ” 
  &&  “ (i <= n) ” 
  &&  “ ((Zlength ((sublist (start) (i) (input)))) = (i - start )) ” 
  &&  “ (all_ascii (sublist (start) (i) (input)) ) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= i) ” 
  &&  “ (output_size = (Zlength (output_words))) ” 
  &&  “ (output_size = (Zlength (output_ptrs_2))) ” 
  &&  “ (output_size <= cap) ” 
  &&  “ (cap = (n + 1 )) ” 
  &&  “ (0 <= cap) ” 
  &&  “ (cap < INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (closing_delimiter_101 input i n ) ” 
  &&  “ (split_prefix_state_101 input i start output_words ) ” 
  &&  “ (problem_101_pre_z input ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ ((2 * ((string_length (input)) + 1 ) ) < INT_MAX) ”
  &&  (CharArray.seg input_ptr 0 start (sublist (0) (start) ((c_string (input)))) )
  **  (CharArray.full (input_ptr + (start * sizeof(CHAR) ) ) (i - start ) (sublist (start) (i) (input)) )
  **  (CharArray.seg input_ptr i (n + 1 ) (sublist (i) ((n + 1 )) ((c_string (input)))) )
  **  (CharArray.undef_full retval (i - start ) )
  **  (CharArray.undef_seg retval (i - start ) ((i - start ) + 1 ) )
  **  (words_rows_heap_101 output_ptrs_2 output_words )
).

Definition words_string_entail_wit_3 := 
(
forall (input_ptr: Z) (input: (@list Z)) (input_pre: (@list Z)) (input_post: (@list Z)) (output_words_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (start: Z) (i: Z) (n: Z) (len: Z) (output_size: Z) (cap: Z) (out: Z) (data: Z) (w: Z) (retval: Z) (PreH1 : (0 <= len)) (PreH2 : (retval = w)) (PreH3 : (0 <= start)) (PreH4 : (start < i)) (PreH5 : (i <= n)) (PreH6 : (len = (i - start ))) (PreH7 : ((Zlength ((sublist (start) (i) (input)))) = len)) (PreH8 : (all_ascii (sublist (start) (i) (input)) )) (PreH9 : (input_pre = (sublist (0) (start) ((c_string (input)))))) (PreH10 : (input_post = (sublist (i) ((n + 1 )) ((c_string (input)))))) (PreH11 : (n = (string_length (input)))) (PreH12 : (0 <= output_size)) (PreH13 : (output_size <= i)) (PreH14 : (output_size = (Zlength (output_words_2)))) (PreH15 : (output_size = (Zlength (output_ptrs_2)))) (PreH16 : (output_size <= cap)) (PreH17 : (cap = (n + 1 ))) (PreH18 : (0 <= cap)) (PreH19 : (cap < INT_MAX)) (PreH20 : (out <> 0)) (PreH21 : (data <> 0)) (PreH22 : (w <> 0)) (PreH23 : (closing_delimiter_101 input i n )) (PreH24 : (split_prefix_state_101 input i start output_words_2 )) (PreH25 : (problem_101_pre_z input )) (PreH26 : (valid_string input )) (PreH27 : ((2 * ((string_length (input)) + 1 ) ) < INT_MAX)) ,
  (CharArray.full w (len + 1 ) (app ((sublist (start) (i) (input))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg w (len + 1 ) (len + 1 ) )
  **  (CharArray.full (input_ptr + (start * sizeof(CHAR) ) ) len (sublist (start) (i) (input)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (CharArray.seg input_ptr 0 start input_pre )
  **  (CharArray.seg input_ptr i (n + 1 ) input_post )
  **  (PtrArray.seg data 0 output_size output_ptrs_2 )
  **  (PtrArray.undef_seg data output_size cap )
  **  (words_rows_heap_101 output_ptrs_2 output_words_2 )
|--
  EX (output_ptrs: (@list Z))  (output_words: (@list (@list Z))) ,
  “ (0 <= start) ” 
  &&  “ (start < i) ” 
  &&  “ (i <= n) ” 
  &&  “ (len = (i - start )) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= i) ” 
  &&  “ (output_size = (Zlength (output_words))) ” 
  &&  “ (output_size = (Zlength (output_ptrs))) ” 
  &&  “ (output_size < cap) ” 
  &&  “ (cap = (n + 1 )) ” 
  &&  “ (0 <= cap) ” 
  &&  “ (cap < INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (w <> 0) ” 
  &&  “ (closing_delimiter_101 input i n ) ” 
  &&  “ (split_prefix_state_101 input i start output_words ) ” 
  &&  “ (problem_101_pre_z input ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ ((2 * ((string_length (input)) + 1 ) ) < INT_MAX) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (store_string input_ptr input )
  **  (CharArray.full w (Zlength ((c_string ((sublist (start) (i) (input)))))) (c_string ((sublist (start) (i) (input)))) )
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size cap )
  **  (words_rows_heap_101 output_ptrs output_words )
) \/
(
forall (input_ptr: Z) (input: (@list Z)) (input_pre: (@list Z)) (input_post: (@list Z)) (output_words_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (start: Z) (i: Z) (n: Z) (len: Z) (output_size: Z) (cap: Z) (out: Z) (data: Z) (w: Z) (retval: Z) (PreH1 : (0 <= (len + 1 ))) (PreH2 : (0 <= len)) (PreH3 : (retval = w)) (PreH4 : (0 <= start)) (PreH5 : (start < i)) (PreH6 : (i <= n)) (PreH7 : (len = (i - start ))) (PreH8 : ((Zlength ((sublist (start) (i) (input)))) = len)) (PreH9 : (all_ascii (sublist (start) (i) (input)) )) (PreH10 : (input_pre = (sublist (0) (start) ((c_string (input)))))) (PreH11 : (input_post = (sublist (i) ((n + 1 )) ((c_string (input)))))) (PreH12 : (n = (string_length (input)))) (PreH13 : (0 <= output_size)) (PreH14 : (output_size <= i)) (PreH15 : (output_size = (Zlength (output_words_2)))) (PreH16 : (output_size = (Zlength (output_ptrs_2)))) (PreH17 : (output_size <= cap)) (PreH18 : (cap = (n + 1 ))) (PreH19 : (0 <= cap)) (PreH20 : (cap < INT_MAX)) (PreH21 : (out <> 0)) (PreH22 : (data <> 0)) (PreH23 : (w <> 0)) (PreH24 : (closing_delimiter_101 input i n )) (PreH25 : (split_prefix_state_101 input i start output_words_2 )) (PreH26 : (problem_101_pre_z input )) (PreH27 : (valid_string input )) (PreH28 : ((2 * ((string_length (input)) + 1 ) ) < INT_MAX)) ,
  (CharArray.full w (len + 1 ) (app ((sublist (start) (i) (input))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full (input_ptr + (start * sizeof(CHAR) ) ) len (sublist (start) (i) (input)) )
  **  (CharArray.seg input_ptr 0 start input_pre )
  **  (CharArray.seg input_ptr i (n + 1 ) input_post )
  **  (words_rows_heap_101 output_ptrs_2 output_words_2 )
|--
  EX (output_words: (@list (@list Z))) ,
  “ (0 <= start) ” 
  &&  “ (start < i) ” 
  &&  “ (i <= n) ” 
  &&  “ (len = (i - start )) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= i) ” 
  &&  “ (output_size = (Zlength (output_words))) ” 
  &&  “ (output_size = (Zlength (output_ptrs_2))) ” 
  &&  “ (output_size < cap) ” 
  &&  “ (cap = (n + 1 )) ” 
  &&  “ (0 <= cap) ” 
  &&  “ (cap < INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (w <> 0) ” 
  &&  “ (closing_delimiter_101 input i n ) ” 
  &&  “ (split_prefix_state_101 input i start output_words ) ” 
  &&  “ (problem_101_pre_z input ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ ((2 * ((string_length (input)) + 1 ) ) < INT_MAX) ”
  &&  (CharArray.full input_ptr ((string_length (input)) + 1 ) (c_string (input)) )
  **  (CharArray.full w (Zlength ((c_string ((sublist (start) (i) (input)))))) (c_string ((sublist (start) (i) (input)))) )
  **  (words_rows_heap_101 output_ptrs_2 output_words )
).

Definition words_string_entail_wit_4_1 := 
(
forall (input_ptr: Z) (input: (@list Z)) (output_words_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (start: Z) (i: Z) (n: Z) (len: Z) (output_size: Z) (cap: Z) (out: Z) (data: Z) (w: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (0 <= (Zlength ((c_string ((sublist (start) (i) (input)))))))) (PreH3 : (0 <= start)) (PreH4 : (start < i)) (PreH5 : (i <= n)) (PreH6 : (len = (i - start ))) (PreH7 : (n = (string_length (input)))) (PreH8 : (0 <= output_size)) (PreH9 : (output_size <= i)) (PreH10 : (output_size = (Zlength (output_words_2)))) (PreH11 : (output_size = (Zlength (output_ptrs_2)))) (PreH12 : (output_size < cap)) (PreH13 : (cap = (n + 1 ))) (PreH14 : (0 <= cap)) (PreH15 : (cap < INT_MAX)) (PreH16 : (out <> 0)) (PreH17 : (data <> 0)) (PreH18 : (w <> 0)) (PreH19 : (closing_delimiter_101 input i n )) (PreH20 : (split_prefix_state_101 input i start output_words_2 )) (PreH21 : (problem_101_pre_z input )) (PreH22 : (valid_string input )) (PreH23 : ((2 * ((string_length (input)) + 1 ) ) < INT_MAX)) ,
  (PtrArray.seg data 0 (output_size + 1 ) (app (output_ptrs_2) ((cons (w) ((@nil Z))))) )
  **  (PtrArray.undef_seg data (output_size + 1 ) cap )
  **  (CharArray.full input_ptr ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (output_size + 1 ))
  **  (CharArray.full w (Zlength ((c_string ((sublist (start) (i) (input)))))) (c_string ((sublist (start) (i) (input)))) )
  **  (words_rows_heap_101 output_ptrs_2 output_words_2 )
|--
  EX (output_ptrs: (@list Z))  (output_words: (@list (@list Z))) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (n + 1 )) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (0 <= (output_size + 1 )) ” 
  &&  “ ((output_size + 1 ) <= (i + 1 )) ” 
  &&  “ ((output_size + 1 ) = (Zlength (output_words))) ” 
  &&  “ ((output_size + 1 ) = (Zlength (output_ptrs))) ” 
  &&  “ (cap = (n + 1 )) ” 
  &&  “ (0 <= cap) ” 
  &&  “ (cap < INT_MAX) ” 
  &&  “ ((output_size + 1 ) <= cap) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (split_prefix_state_101 input (i + 1 ) (-1) output_words ) ” 
  &&  “ (problem_101_pre_z input ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ ((2 * ((string_length (input)) + 1 ) ) < INT_MAX) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (output_size + 1 ))
  **  (store_string input_ptr input )
  **  (PtrArray.seg data 0 (output_size + 1 ) output_ptrs )
  **  (PtrArray.undef_seg data (output_size + 1 ) cap )
  **  (words_rows_heap_101 output_ptrs output_words )
) \/
(
forall (input: (@list Z)) (output_words_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (start: Z) (i: Z) (n: Z) (len: Z) (output_size: Z) (cap: Z) (out: Z) (data: Z) (w: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (0 <= (Zlength ((c_string ((sublist (start) (i) (input)))))))) (PreH3 : (0 <= start)) (PreH4 : (start < i)) (PreH5 : (i <= n)) (PreH6 : (len = (i - start ))) (PreH7 : (n = (string_length (input)))) (PreH8 : (0 <= output_size)) (PreH9 : (output_size <= i)) (PreH10 : (output_size = (Zlength (output_words_2)))) (PreH11 : (output_size = (Zlength (output_ptrs_2)))) (PreH12 : (output_size < cap)) (PreH13 : (cap = (n + 1 ))) (PreH14 : (0 <= cap)) (PreH15 : (cap < INT_MAX)) (PreH16 : (out <> 0)) (PreH17 : (data <> 0)) (PreH18 : (w <> 0)) (PreH19 : (closing_delimiter_101 input i n )) (PreH20 : (split_prefix_state_101 input i start output_words_2 )) (PreH21 : (problem_101_pre_z input )) (PreH22 : (valid_string input )) (PreH23 : ((2 * ((string_length (input)) + 1 ) ) < INT_MAX)) ,
  (CharArray.full w (Zlength ((c_string ((sublist (start) (i) (input)))))) (c_string ((sublist (start) (i) (input)))) )
  **  (words_rows_heap_101 output_ptrs_2 output_words_2 )
|--
  EX (output_words: (@list (@list Z))) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (n + 1 )) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (0 <= (output_size + 1 )) ” 
  &&  “ ((output_size + 1 ) <= (i + 1 )) ” 
  &&  “ ((output_size + 1 ) = (Zlength (output_words))) ” 
  &&  “ ((output_size + 1 ) = (Zlength ((app (output_ptrs_2) ((cons (w) ((@nil Z)))))))) ” 
  &&  “ (cap = (n + 1 )) ” 
  &&  “ (0 <= cap) ” 
  &&  “ (cap < INT_MAX) ” 
  &&  “ ((output_size + 1 ) <= cap) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (split_prefix_state_101 input (i + 1 ) (-1) output_words ) ” 
  &&  “ (problem_101_pre_z input ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ ((2 * ((string_length (input)) + 1 ) ) < INT_MAX) ”
  &&  (words_rows_heap_101 (app (output_ptrs_2) ((cons (w) ((@nil Z))))) output_words )
).

Definition words_string_entail_wit_4_2 := 
(
forall (input_ptr: Z) (input: (@list Z)) (start: Z) (data: Z) (out: Z) (cap: Z) (output_ptrs_2: (@list Z)) (output_words_2: (@list (@list Z))) (output_size: Z) (n: Z) (i: Z) (PreH1 : (start < 0)) (PreH2 : (i >= n)) (PreH3 : (i <= n)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n + 1 ))) (PreH6 : (n = (string_length (input)))) (PreH7 : (0 <= output_size)) (PreH8 : (output_size <= i)) (PreH9 : (output_size = (Zlength (output_words_2)))) (PreH10 : (output_size = (Zlength (output_ptrs_2)))) (PreH11 : (cap = (n + 1 ))) (PreH12 : (0 <= cap)) (PreH13 : (cap < INT_MAX)) (PreH14 : (output_size <= cap)) (PreH15 : (out <> 0)) (PreH16 : (data <> 0)) (PreH17 : (split_prefix_state_101 input i start output_words_2 )) (PreH18 : (problem_101_pre_z input )) (PreH19 : (valid_string input )) (PreH20 : ((2 * ((string_length (input)) + 1 ) ) < INT_MAX)) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (store_string input_ptr input )
  **  (PtrArray.seg data 0 output_size output_ptrs_2 )
  **  (PtrArray.undef_seg data output_size cap )
  **  (words_rows_heap_101 output_ptrs_2 output_words_2 )
|--
  EX (output_ptrs: (@list Z))  (output_words: (@list (@list Z))) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (n + 1 )) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= (i + 1 )) ” 
  &&  “ (output_size = (Zlength (output_words))) ” 
  &&  “ (output_size = (Zlength (output_ptrs))) ” 
  &&  “ (cap = (n + 1 )) ” 
  &&  “ (0 <= cap) ” 
  &&  “ (cap < INT_MAX) ” 
  &&  “ (output_size <= cap) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (split_prefix_state_101 input (i + 1 ) start output_words ) ” 
  &&  “ (problem_101_pre_z input ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ ((2 * ((string_length (input)) + 1 ) ) < INT_MAX) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (store_string input_ptr input )
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size cap )
  **  (words_rows_heap_101 output_ptrs output_words )
) \/
(
forall (input: (@list Z)) (start: Z) (data: Z) (out: Z) (cap: Z) (output_ptrs_2: (@list Z)) (output_words_2: (@list (@list Z))) (output_size: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (start < 0)) (PreH3 : (i >= n)) (PreH4 : (i <= n)) (PreH5 : (0 <= i)) (PreH6 : (i <= (n + 1 ))) (PreH7 : (n = (string_length (input)))) (PreH8 : (0 <= output_size)) (PreH9 : (output_size <= i)) (PreH10 : (output_size = (Zlength (output_words_2)))) (PreH11 : (output_size = (Zlength (output_ptrs_2)))) (PreH12 : (cap = (n + 1 ))) (PreH13 : (0 <= cap)) (PreH14 : (cap < INT_MAX)) (PreH15 : (output_size <= cap)) (PreH16 : (out <> 0)) (PreH17 : (data <> 0)) (PreH18 : (split_prefix_state_101 input i start output_words_2 )) (PreH19 : (problem_101_pre_z input )) (PreH20 : (valid_string input )) (PreH21 : ((2 * ((string_length (input)) + 1 ) ) < INT_MAX)) ,
  (words_rows_heap_101 output_ptrs_2 output_words_2 )
|--
  EX (output_words: (@list (@list Z))) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (n + 1 )) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= (i + 1 )) ” 
  &&  “ (output_size = (Zlength (output_words))) ” 
  &&  “ (output_size = (Zlength (output_ptrs_2))) ” 
  &&  “ (cap = (n + 1 )) ” 
  &&  “ (0 <= cap) ” 
  &&  “ (cap < INT_MAX) ” 
  &&  “ (output_size <= cap) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (split_prefix_state_101 input (i + 1 ) start output_words ) ” 
  &&  “ (problem_101_pre_z input ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ ((2 * ((string_length (input)) + 1 ) ) < INT_MAX) ”
  &&  (words_rows_heap_101 output_ptrs_2 output_words )
).

Definition words_string_entail_wit_4_3 := 
(
forall (input_ptr: Z) (input: (@list Z)) (start: Z) (data: Z) (out: Z) (cap: Z) (output_ptrs_2: (@list Z)) (output_words_2: (@list (@list Z))) (output_size: Z) (n: Z) (i: Z) (PreH1 : (start < 0)) (PreH2 : ((Znth i (c_string (input)) 0) = 32)) (PreH3 : (i < n)) (PreH4 : (i <= n)) (PreH5 : (0 <= i)) (PreH6 : (i <= (n + 1 ))) (PreH7 : (n = (string_length (input)))) (PreH8 : (0 <= output_size)) (PreH9 : (output_size <= i)) (PreH10 : (output_size = (Zlength (output_words_2)))) (PreH11 : (output_size = (Zlength (output_ptrs_2)))) (PreH12 : (cap = (n + 1 ))) (PreH13 : (0 <= cap)) (PreH14 : (cap < INT_MAX)) (PreH15 : (output_size <= cap)) (PreH16 : (out <> 0)) (PreH17 : (data <> 0)) (PreH18 : (split_prefix_state_101 input i start output_words_2 )) (PreH19 : (problem_101_pre_z input )) (PreH20 : (valid_string input )) (PreH21 : ((2 * ((string_length (input)) + 1 ) ) < INT_MAX)) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (store_string input_ptr input )
  **  (PtrArray.seg data 0 output_size output_ptrs_2 )
  **  (PtrArray.undef_seg data output_size cap )
  **  (words_rows_heap_101 output_ptrs_2 output_words_2 )
|--
  EX (output_ptrs: (@list Z))  (output_words: (@list (@list Z))) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (n + 1 )) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= (i + 1 )) ” 
  &&  “ (output_size = (Zlength (output_words))) ” 
  &&  “ (output_size = (Zlength (output_ptrs))) ” 
  &&  “ (cap = (n + 1 )) ” 
  &&  “ (0 <= cap) ” 
  &&  “ (cap < INT_MAX) ” 
  &&  “ (output_size <= cap) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (split_prefix_state_101 input (i + 1 ) start output_words ) ” 
  &&  “ (problem_101_pre_z input ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ ((2 * ((string_length (input)) + 1 ) ) < INT_MAX) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (store_string input_ptr input )
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size cap )
  **  (words_rows_heap_101 output_ptrs output_words )
) \/
(
forall (input: (@list Z)) (start: Z) (data: Z) (out: Z) (cap: Z) (output_ptrs_2: (@list Z)) (output_words_2: (@list (@list Z))) (output_size: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (start < 0)) (PreH3 : ((Znth i (c_string (input)) 0) = 32)) (PreH4 : (i < n)) (PreH5 : (i <= n)) (PreH6 : (0 <= i)) (PreH7 : (i <= (n + 1 ))) (PreH8 : (n = (string_length (input)))) (PreH9 : (0 <= output_size)) (PreH10 : (output_size <= i)) (PreH11 : (output_size = (Zlength (output_words_2)))) (PreH12 : (output_size = (Zlength (output_ptrs_2)))) (PreH13 : (cap = (n + 1 ))) (PreH14 : (0 <= cap)) (PreH15 : (cap < INT_MAX)) (PreH16 : (output_size <= cap)) (PreH17 : (out <> 0)) (PreH18 : (data <> 0)) (PreH19 : (split_prefix_state_101 input i start output_words_2 )) (PreH20 : (problem_101_pre_z input )) (PreH21 : (valid_string input )) (PreH22 : ((2 * ((string_length (input)) + 1 ) ) < INT_MAX)) ,
  (words_rows_heap_101 output_ptrs_2 output_words_2 )
|--
  EX (output_words: (@list (@list Z))) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (n + 1 )) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= (i + 1 )) ” 
  &&  “ (output_size = (Zlength (output_words))) ” 
  &&  “ (output_size = (Zlength (output_ptrs_2))) ” 
  &&  “ (cap = (n + 1 )) ” 
  &&  “ (0 <= cap) ” 
  &&  “ (cap < INT_MAX) ” 
  &&  “ (output_size <= cap) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (split_prefix_state_101 input (i + 1 ) start output_words ) ” 
  &&  “ (problem_101_pre_z input ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ ((2 * ((string_length (input)) + 1 ) ) < INT_MAX) ”
  &&  (words_rows_heap_101 output_ptrs_2 output_words )
).

Definition words_string_entail_wit_4_4 := 
(
forall (input_ptr: Z) (input: (@list Z)) (start: Z) (data: Z) (out: Z) (cap: Z) (output_ptrs_2: (@list Z)) (output_words_2: (@list (@list Z))) (output_size: Z) (n: Z) (i: Z) (PreH1 : (start < 0)) (PreH2 : ((Znth i (c_string (input)) 0) = 44)) (PreH3 : ((Znth i (c_string (input)) 0) <> 32)) (PreH4 : (i < n)) (PreH5 : (i <= n)) (PreH6 : (0 <= i)) (PreH7 : (i <= (n + 1 ))) (PreH8 : (n = (string_length (input)))) (PreH9 : (0 <= output_size)) (PreH10 : (output_size <= i)) (PreH11 : (output_size = (Zlength (output_words_2)))) (PreH12 : (output_size = (Zlength (output_ptrs_2)))) (PreH13 : (cap = (n + 1 ))) (PreH14 : (0 <= cap)) (PreH15 : (cap < INT_MAX)) (PreH16 : (output_size <= cap)) (PreH17 : (out <> 0)) (PreH18 : (data <> 0)) (PreH19 : (split_prefix_state_101 input i start output_words_2 )) (PreH20 : (problem_101_pre_z input )) (PreH21 : (valid_string input )) (PreH22 : ((2 * ((string_length (input)) + 1 ) ) < INT_MAX)) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (store_string input_ptr input )
  **  (PtrArray.seg data 0 output_size output_ptrs_2 )
  **  (PtrArray.undef_seg data output_size cap )
  **  (words_rows_heap_101 output_ptrs_2 output_words_2 )
|--
  EX (output_ptrs: (@list Z))  (output_words: (@list (@list Z))) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (n + 1 )) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= (i + 1 )) ” 
  &&  “ (output_size = (Zlength (output_words))) ” 
  &&  “ (output_size = (Zlength (output_ptrs))) ” 
  &&  “ (cap = (n + 1 )) ” 
  &&  “ (0 <= cap) ” 
  &&  “ (cap < INT_MAX) ” 
  &&  “ (output_size <= cap) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (split_prefix_state_101 input (i + 1 ) start output_words ) ” 
  &&  “ (problem_101_pre_z input ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ ((2 * ((string_length (input)) + 1 ) ) < INT_MAX) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (store_string input_ptr input )
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size cap )
  **  (words_rows_heap_101 output_ptrs output_words )
) \/
(
forall (input: (@list Z)) (start: Z) (data: Z) (out: Z) (cap: Z) (output_ptrs_2: (@list Z)) (output_words_2: (@list (@list Z))) (output_size: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (start < 0)) (PreH3 : ((Znth i (c_string (input)) 0) = 44)) (PreH4 : ((Znth i (c_string (input)) 0) <> 32)) (PreH5 : (i < n)) (PreH6 : (i <= n)) (PreH7 : (0 <= i)) (PreH8 : (i <= (n + 1 ))) (PreH9 : (n = (string_length (input)))) (PreH10 : (0 <= output_size)) (PreH11 : (output_size <= i)) (PreH12 : (output_size = (Zlength (output_words_2)))) (PreH13 : (output_size = (Zlength (output_ptrs_2)))) (PreH14 : (cap = (n + 1 ))) (PreH15 : (0 <= cap)) (PreH16 : (cap < INT_MAX)) (PreH17 : (output_size <= cap)) (PreH18 : (out <> 0)) (PreH19 : (data <> 0)) (PreH20 : (split_prefix_state_101 input i start output_words_2 )) (PreH21 : (problem_101_pre_z input )) (PreH22 : (valid_string input )) (PreH23 : ((2 * ((string_length (input)) + 1 ) ) < INT_MAX)) ,
  (words_rows_heap_101 output_ptrs_2 output_words_2 )
|--
  EX (output_words: (@list (@list Z))) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (n + 1 )) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= (i + 1 )) ” 
  &&  “ (output_size = (Zlength (output_words))) ” 
  &&  “ (output_size = (Zlength (output_ptrs_2))) ” 
  &&  “ (cap = (n + 1 )) ” 
  &&  “ (0 <= cap) ” 
  &&  “ (cap < INT_MAX) ” 
  &&  “ (output_size <= cap) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (split_prefix_state_101 input (i + 1 ) start output_words ) ” 
  &&  “ (problem_101_pre_z input ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ ((2 * ((string_length (input)) + 1 ) ) < INT_MAX) ”
  &&  (words_rows_heap_101 output_ptrs_2 output_words )
).

Definition words_string_entail_wit_4_5 := 
(
forall (input_ptr: Z) (input: (@list Z)) (start: Z) (data: Z) (out: Z) (cap: Z) (output_ptrs_2: (@list Z)) (output_words_2: (@list (@list Z))) (output_size: Z) (n: Z) (i: Z) (PreH1 : (start < 0)) (PreH2 : ((Znth i (c_string (input)) 0) <> 44)) (PreH3 : ((Znth i (c_string (input)) 0) <> 32)) (PreH4 : (i < n)) (PreH5 : (i <= n)) (PreH6 : (0 <= i)) (PreH7 : (i <= (n + 1 ))) (PreH8 : (n = (string_length (input)))) (PreH9 : (0 <= output_size)) (PreH10 : (output_size <= i)) (PreH11 : (output_size = (Zlength (output_words_2)))) (PreH12 : (output_size = (Zlength (output_ptrs_2)))) (PreH13 : (cap = (n + 1 ))) (PreH14 : (0 <= cap)) (PreH15 : (cap < INT_MAX)) (PreH16 : (output_size <= cap)) (PreH17 : (out <> 0)) (PreH18 : (data <> 0)) (PreH19 : (split_prefix_state_101 input i start output_words_2 )) (PreH20 : (problem_101_pre_z input )) (PreH21 : (valid_string input )) (PreH22 : ((2 * ((string_length (input)) + 1 ) ) < INT_MAX)) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (store_string input_ptr input )
  **  (PtrArray.seg data 0 output_size output_ptrs_2 )
  **  (PtrArray.undef_seg data output_size cap )
  **  (words_rows_heap_101 output_ptrs_2 output_words_2 )
|--
  EX (output_ptrs: (@list Z))  (output_words: (@list (@list Z))) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (n + 1 )) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= (i + 1 )) ” 
  &&  “ (output_size = (Zlength (output_words))) ” 
  &&  “ (output_size = (Zlength (output_ptrs))) ” 
  &&  “ (cap = (n + 1 )) ” 
  &&  “ (0 <= cap) ” 
  &&  “ (cap < INT_MAX) ” 
  &&  “ (output_size <= cap) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (split_prefix_state_101 input (i + 1 ) i output_words ) ” 
  &&  “ (problem_101_pre_z input ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ ((2 * ((string_length (input)) + 1 ) ) < INT_MAX) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (store_string input_ptr input )
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size cap )
  **  (words_rows_heap_101 output_ptrs output_words )
) \/
(
forall (input: (@list Z)) (start: Z) (data: Z) (out: Z) (cap: Z) (output_ptrs_2: (@list Z)) (output_words_2: (@list (@list Z))) (output_size: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (start < 0)) (PreH3 : ((Znth i (c_string (input)) 0) <> 44)) (PreH4 : ((Znth i (c_string (input)) 0) <> 32)) (PreH5 : (i < n)) (PreH6 : (i <= n)) (PreH7 : (0 <= i)) (PreH8 : (i <= (n + 1 ))) (PreH9 : (n = (string_length (input)))) (PreH10 : (0 <= output_size)) (PreH11 : (output_size <= i)) (PreH12 : (output_size = (Zlength (output_words_2)))) (PreH13 : (output_size = (Zlength (output_ptrs_2)))) (PreH14 : (cap = (n + 1 ))) (PreH15 : (0 <= cap)) (PreH16 : (cap < INT_MAX)) (PreH17 : (output_size <= cap)) (PreH18 : (out <> 0)) (PreH19 : (data <> 0)) (PreH20 : (split_prefix_state_101 input i start output_words_2 )) (PreH21 : (problem_101_pre_z input )) (PreH22 : (valid_string input )) (PreH23 : ((2 * ((string_length (input)) + 1 ) ) < INT_MAX)) ,
  (words_rows_heap_101 output_ptrs_2 output_words_2 )
|--
  EX (output_words: (@list (@list Z))) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (n + 1 )) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= (i + 1 )) ” 
  &&  “ (output_size = (Zlength (output_words))) ” 
  &&  “ (output_size = (Zlength (output_ptrs_2))) ” 
  &&  “ (cap = (n + 1 )) ” 
  &&  “ (0 <= cap) ” 
  &&  “ (cap < INT_MAX) ” 
  &&  “ (output_size <= cap) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (split_prefix_state_101 input (i + 1 ) i output_words ) ” 
  &&  “ (problem_101_pre_z input ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ ((2 * ((string_length (input)) + 1 ) ) < INT_MAX) ”
  &&  (words_rows_heap_101 output_ptrs_2 output_words )
).

Definition words_string_entail_wit_4_6 := 
(
forall (input_ptr: Z) (input: (@list Z)) (start: Z) (data: Z) (out: Z) (cap: Z) (output_ptrs_2: (@list Z)) (output_words_2: (@list (@list Z))) (output_size: Z) (n: Z) (i: Z) (PreH1 : (start >= 0)) (PreH2 : ((Znth i (c_string (input)) 0) <> 44)) (PreH3 : ((Znth i (c_string (input)) 0) <> 32)) (PreH4 : (i < n)) (PreH5 : (i <= n)) (PreH6 : (0 <= i)) (PreH7 : (i <= (n + 1 ))) (PreH8 : (n = (string_length (input)))) (PreH9 : (0 <= output_size)) (PreH10 : (output_size <= i)) (PreH11 : (output_size = (Zlength (output_words_2)))) (PreH12 : (output_size = (Zlength (output_ptrs_2)))) (PreH13 : (cap = (n + 1 ))) (PreH14 : (0 <= cap)) (PreH15 : (cap < INT_MAX)) (PreH16 : (output_size <= cap)) (PreH17 : (out <> 0)) (PreH18 : (data <> 0)) (PreH19 : (split_prefix_state_101 input i start output_words_2 )) (PreH20 : (problem_101_pre_z input )) (PreH21 : (valid_string input )) (PreH22 : ((2 * ((string_length (input)) + 1 ) ) < INT_MAX)) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (store_string input_ptr input )
  **  (PtrArray.seg data 0 output_size output_ptrs_2 )
  **  (PtrArray.undef_seg data output_size cap )
  **  (words_rows_heap_101 output_ptrs_2 output_words_2 )
|--
  EX (output_ptrs: (@list Z))  (output_words: (@list (@list Z))) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (n + 1 )) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= (i + 1 )) ” 
  &&  “ (output_size = (Zlength (output_words))) ” 
  &&  “ (output_size = (Zlength (output_ptrs))) ” 
  &&  “ (cap = (n + 1 )) ” 
  &&  “ (0 <= cap) ” 
  &&  “ (cap < INT_MAX) ” 
  &&  “ (output_size <= cap) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (split_prefix_state_101 input (i + 1 ) start output_words ) ” 
  &&  “ (problem_101_pre_z input ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ ((2 * ((string_length (input)) + 1 ) ) < INT_MAX) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (store_string input_ptr input )
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size cap )
  **  (words_rows_heap_101 output_ptrs output_words )
) \/
(
forall (input: (@list Z)) (start: Z) (data: Z) (out: Z) (cap: Z) (output_ptrs_2: (@list Z)) (output_words_2: (@list (@list Z))) (output_size: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (start >= 0)) (PreH3 : ((Znth i (c_string (input)) 0) <> 44)) (PreH4 : ((Znth i (c_string (input)) 0) <> 32)) (PreH5 : (i < n)) (PreH6 : (i <= n)) (PreH7 : (0 <= i)) (PreH8 : (i <= (n + 1 ))) (PreH9 : (n = (string_length (input)))) (PreH10 : (0 <= output_size)) (PreH11 : (output_size <= i)) (PreH12 : (output_size = (Zlength (output_words_2)))) (PreH13 : (output_size = (Zlength (output_ptrs_2)))) (PreH14 : (cap = (n + 1 ))) (PreH15 : (0 <= cap)) (PreH16 : (cap < INT_MAX)) (PreH17 : (output_size <= cap)) (PreH18 : (out <> 0)) (PreH19 : (data <> 0)) (PreH20 : (split_prefix_state_101 input i start output_words_2 )) (PreH21 : (problem_101_pre_z input )) (PreH22 : (valid_string input )) (PreH23 : ((2 * ((string_length (input)) + 1 ) ) < INT_MAX)) ,
  (words_rows_heap_101 output_ptrs_2 output_words_2 )
|--
  EX (output_words: (@list (@list Z))) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (n + 1 )) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= (i + 1 )) ” 
  &&  “ (output_size = (Zlength (output_words))) ” 
  &&  “ (output_size = (Zlength (output_ptrs_2))) ” 
  &&  “ (cap = (n + 1 )) ” 
  &&  “ (0 <= cap) ” 
  &&  “ (cap < INT_MAX) ” 
  &&  “ (output_size <= cap) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (split_prefix_state_101 input (i + 1 ) start output_words ) ” 
  &&  “ (problem_101_pre_z input ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ ((2 * ((string_length (input)) + 1 ) ) < INT_MAX) ”
  &&  (words_rows_heap_101 output_ptrs_2 output_words )
).

Definition words_string_return_wit_1 := 
(
forall (input_ptr: Z) (input: (@list Z)) (start: Z) (data_2: Z) (out: Z) (cap_2: Z) (output_ptrs_2: (@list Z)) (output_words_2: (@list (@list Z))) (output_size_2: Z) (n: Z) (i: Z) (PreH1 : (i > n)) (PreH2 : (0 <= i)) (PreH3 : (i <= (n + 1 ))) (PreH4 : (n = (string_length (input)))) (PreH5 : (0 <= output_size_2)) (PreH6 : (output_size_2 <= i)) (PreH7 : (output_size_2 = (Zlength (output_words_2)))) (PreH8 : (output_size_2 = (Zlength (output_ptrs_2)))) (PreH9 : (cap_2 = (n + 1 ))) (PreH10 : (0 <= cap_2)) (PreH11 : (cap_2 < INT_MAX)) (PreH12 : (output_size_2 <= cap_2)) (PreH13 : (out <> 0)) (PreH14 : (data_2 <> 0)) (PreH15 : (split_prefix_state_101 input i start output_words_2 )) (PreH16 : (problem_101_pre_z input )) (PreH17 : (valid_string input )) (PreH18 : ((2 * ((string_length (input)) + 1 ) ) < INT_MAX)) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data_2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size_2)
  **  (store_string input_ptr input )
  **  (PtrArray.seg data_2 0 output_size_2 output_ptrs_2 )
  **  (PtrArray.undef_seg data_2 output_size_2 cap_2 )
  **  (words_rows_heap_101 output_ptrs_2 output_words_2 )
|--
  EX (cap: Z)  (output_ptrs: (@list Z))  (output_words: (@list (@list Z)))  (output_size: Z)  (data: Z) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= ((string_length (input)) + 1 )) ” 
  &&  “ (output_size = (Zlength (output_words))) ” 
  &&  “ (output_size = (Zlength (output_ptrs))) ” 
  &&  “ (output_size <= cap) ” 
  &&  “ (cap < INT_MAX) ” 
  &&  “ (problem_101_spec_z input output_words ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (store_string input_ptr input )
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size cap )
  **  (words_rows_heap_101 output_ptrs output_words )
) \/
(
forall (input: (@list Z)) (start: Z) (data_2: Z) (out: Z) (cap_2: Z) (output_ptrs_2: (@list Z)) (output_words_2: (@list (@list Z))) (output_size_2: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (i > n)) (PreH3 : (0 <= i)) (PreH4 : (i <= (n + 1 ))) (PreH5 : (n = (string_length (input)))) (PreH6 : (0 <= output_size_2)) (PreH7 : (output_size_2 <= i)) (PreH8 : (output_size_2 = (Zlength (output_words_2)))) (PreH9 : (output_size_2 = (Zlength (output_ptrs_2)))) (PreH10 : (cap_2 = (n + 1 ))) (PreH11 : (0 <= cap_2)) (PreH12 : (cap_2 < INT_MAX)) (PreH13 : (output_size_2 <= cap_2)) (PreH14 : (out <> 0)) (PreH15 : (data_2 <> 0)) (PreH16 : (split_prefix_state_101 input i start output_words_2 )) (PreH17 : (problem_101_pre_z input )) (PreH18 : (valid_string input )) (PreH19 : ((2 * ((string_length (input)) + 1 ) ) < INT_MAX)) ,
  (PtrArray.seg data_2 0 output_size_2 output_ptrs_2 )
  **  (PtrArray.undef_seg data_2 output_size_2 cap_2 )
  **  (words_rows_heap_101 output_ptrs_2 output_words_2 )
|--
  EX (cap: Z)  (output_ptrs: (@list Z))  (output_words: (@list (@list Z))) ,
  “ (output_size_2 = (Zlength (output_words))) ” 
  &&  “ (output_size_2 = (Zlength (output_words))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data_2 <> 0) ” 
  &&  “ (0 <= (Zlength (output_words))) ” 
  &&  “ ((Zlength (output_words)) <= ((string_length (input)) + 1 )) ” 
  &&  “ ((Zlength (output_words)) = (Zlength (output_ptrs))) ” 
  &&  “ ((Zlength (output_words)) <= cap) ” 
  &&  “ (cap < INT_MAX) ” 
  &&  “ (problem_101_spec_z input output_words ) ”
  &&  (PtrArray.seg data_2 0 (Zlength (output_words)) output_ptrs )
  **  (PtrArray.undef_seg data_2 (Zlength (output_words)) cap )
  **  (words_rows_heap_101 output_ptrs output_words )
).

Definition words_string_partial_solve_wit_1 := 
forall (s_pre: Z) (input_ptr: Z) (input: (@list Z)) (PreH1 : (s_pre = input_ptr)) (PreH2 : (problem_101_pre_z input )) (PreH3 : (valid_string input )) (PreH4 : ((2 * ((string_length (input)) + 1 ) ) < INT_MAX)) ,
  (store_string s_pre input )
|--
  “ (0 <= ((string_length (input)) + 1 )) ” 
  &&  “ (s_pre = input_ptr) ” 
  &&  “ (problem_101_pre_z input ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ ((2 * ((string_length (input)) + 1 ) ) < INT_MAX) ”
  &&  (CharArray.full s_pre ((string_length (input)) + 1 ) (c_string (input)) )
.

Definition words_string_partial_solve_wit_2_pure := 
forall (s_pre: Z) (input_ptr: Z) (input: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (s_pre = input_ptr)) (PreH4 : (problem_101_pre_z input )) (PreH5 : (valid_string input )) (PreH6 : ((2 * ((string_length (input)) + 1 ) ) < INT_MAX)) ,
  ((( &( "n" ) )) # Int  |->_)
  **  ((( &( "start" ) )) # Int  |-> (-1))
  **  ((( &( "output_size" ) )) # Int  |-> 0)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (CharArray.full s_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ (valid_string input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ”
.

Definition words_string_partial_solve_wit_2_aux := 
forall (s_pre: Z) (input_ptr: Z) (input: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (s_pre = input_ptr)) (PreH4 : (problem_101_pre_z input )) (PreH5 : (valid_string input )) (PreH6 : ((2 * ((string_length (input)) + 1 ) ) < INT_MAX)) ,
  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (CharArray.full s_pre ((string_length (input)) + 1 ) (c_string (input)) )
|--
  “ (valid_string input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= ((string_length (input)) + 1 )) ” 
  &&  “ (s_pre = input_ptr) ” 
  &&  “ (problem_101_pre_z input ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ ((2 * ((string_length (input)) + 1 ) ) < INT_MAX) ”
  &&  (store_string s_pre input )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
.

Definition words_string_partial_solve_wit_2 := words_string_partial_solve_wit_2_pure -> words_string_partial_solve_wit_2_aux.

Definition words_string_partial_solve_wit_3_pure := 
forall (s_pre: Z) (input_ptr: Z) (input: (@list Z)) (retval_2: Z) (retval: Z) (PreH1 : (retval = (string_length (input)))) (PreH2 : (retval_2 <> 0)) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (s_pre = input_ptr)) (PreH5 : (problem_101_pre_z input )) (PreH6 : (valid_string input )) (PreH7 : ((2 * ((string_length (input)) + 1 ) ) < INT_MAX)) ,
  ((( &( "data" ) )) # Ptr  |->_)
  **  ((( &( "cap" ) )) # Int  |-> (retval + 1 ))
  **  (store_string s_pre input )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "start" ) )) # Int  |-> (-1))
  **  ((( &( "output_size" ) )) # Int  |-> 0)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ (0 <= (retval + 1 )) ” 
  &&  “ ((retval + 1 ) < INT_MAX) ”
.

Definition words_string_partial_solve_wit_3_aux := 
forall (s_pre: Z) (input_ptr: Z) (input: (@list Z)) (retval_2: Z) (retval: Z) (PreH1 : (retval = (string_length (input)))) (PreH2 : (retval_2 <> 0)) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (s_pre = input_ptr)) (PreH5 : (problem_101_pre_z input )) (PreH6 : (valid_string input )) (PreH7 : ((2 * ((string_length (input)) + 1 ) ) < INT_MAX)) ,
  (store_string s_pre input )
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  “ (0 <= (retval + 1 )) ” 
  &&  “ ((retval + 1 ) < INT_MAX) ” 
  &&  “ (retval = (string_length (input))) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (0 <= ((string_length (input)) + 1 )) ” 
  &&  “ (s_pre = input_ptr) ” 
  &&  “ (problem_101_pre_z input ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ ((2 * ((string_length (input)) + 1 ) ) < INT_MAX) ”
  &&  (CharArray.full s_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
.

Definition words_string_partial_solve_wit_3 := words_string_partial_solve_wit_3_pure -> words_string_partial_solve_wit_3_aux.

Definition words_string_partial_solve_wit_4_pure := 
(
forall (input_ptr: Z) (input: (@list Z)) (start: Z) (data: Z) (out: Z) (cap: Z) (output_ptrs: (@list Z)) (output_words: (@list (@list Z))) (output_size: Z) (n: Z) (i: Z) (PreH1 : (start >= 0)) (PreH2 : (i >= n)) (PreH3 : (i <= n)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n + 1 ))) (PreH6 : (n = (string_length (input)))) (PreH7 : (0 <= output_size)) (PreH8 : (output_size <= i)) (PreH9 : (output_size = (Zlength (output_words)))) (PreH10 : (output_size = (Zlength (output_ptrs)))) (PreH11 : (cap = (n + 1 ))) (PreH12 : (0 <= cap)) (PreH13 : (cap < INT_MAX)) (PreH14 : (output_size <= cap)) (PreH15 : (out <> 0)) (PreH16 : (data <> 0)) (PreH17 : (split_prefix_state_101 input i start output_words )) (PreH18 : (problem_101_pre_z input )) (PreH19 : (valid_string input )) (PreH20 : ((2 * ((string_length (input)) + 1 ) ) < INT_MAX)) ,
  ((( &( "w" ) )) # Ptr  |->_)
  **  ((( &( "len" ) )) # Int  |-> (i - start ))
  **  ((( &( "ch" ) )) # Char  |-> 32)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "s" ) )) # Ptr  |-> input_ptr)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (store_string input_ptr input )
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size cap )
  **  (words_rows_heap_101 output_ptrs output_words )
|--
  “ (((i - start ) + 1 ) < INT_MAX) ” 
  &&  “ (0 < ((i - start ) + 1 )) ”
) \/
(
forall (input_ptr: Z) (input: (@list Z)) (start: Z) (data: Z) (out: Z) (cap: Z) (output_ptrs: (@list Z)) (output_words: (@list (@list Z))) (output_size: Z) (n: Z) (i: Z) (PreH1 : (start <= INT_MAX)) (PreH2 : (cap <= INT_MAX)) (PreH3 : (output_size <= INT_MAX)) (PreH4 : (n <= INT_MAX)) (PreH5 : (i <= INT_MAX)) (PreH6 : ((i - start ) <= INT_MAX)) (PreH7 : (start >= INT_MIN)) (PreH8 : (cap >= INT_MIN)) (PreH9 : (output_size >= INT_MIN)) (PreH10 : (n >= INT_MIN)) (PreH11 : (i >= INT_MIN)) (PreH12 : ((i - start ) >= INT_MIN)) (PreH13 : (0 <= ((string_length (input)) + 1 ))) (PreH14 : (start >= 0)) (PreH15 : (i >= n)) (PreH16 : (i <= n)) (PreH17 : (0 <= i)) (PreH18 : (i <= (n + 1 ))) (PreH19 : (n = (string_length (input)))) (PreH20 : (0 <= output_size)) (PreH21 : (output_size <= i)) (PreH22 : (output_size = (Zlength (output_words)))) (PreH23 : (output_size = (Zlength (output_ptrs)))) (PreH24 : (cap = (n + 1 ))) (PreH25 : (0 <= cap)) (PreH26 : (cap < INT_MAX)) (PreH27 : (output_size <= cap)) (PreH28 : (out <> 0)) (PreH29 : (data <> 0)) (PreH30 : (split_prefix_state_101 input i start output_words )) (PreH31 : (problem_101_pre_z input )) (PreH32 : (valid_string input )) (PreH33 : ((2 * ((string_length (input)) + 1 ) ) < INT_MAX)) ,
  (CharArray.full input_ptr ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "w" ) )) # Ptr  |->_)
  **  ((( &( "len" ) )) # Int  |-> (i - start ))
  **  ((( &( "ch" ) )) # Char  |-> 32)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "s" ) )) # Ptr  |-> input_ptr)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size cap )
  **  (words_rows_heap_101 output_ptrs output_words )
|--
  “ (0 < ((i - start ) + 1 )) ”
).

Definition words_string_partial_solve_wit_4_pure_split_goal_1 := 
forall (input_ptr: Z) (input: (@list Z)) (start: Z) (data: Z) (out: Z) (cap: Z) (output_ptrs: (@list Z)) (output_words: (@list (@list Z))) (output_size: Z) (n: Z) (i: Z) (PreH1 : (start <= INT_MAX)) (PreH2 : (cap <= INT_MAX)) (PreH3 : (output_size <= INT_MAX)) (PreH4 : (n <= INT_MAX)) (PreH5 : (i <= INT_MAX)) (PreH6 : ((i - start ) <= INT_MAX)) (PreH7 : (start >= INT_MIN)) (PreH8 : (cap >= INT_MIN)) (PreH9 : (output_size >= INT_MIN)) (PreH10 : (n >= INT_MIN)) (PreH11 : (i >= INT_MIN)) (PreH12 : ((i - start ) >= INT_MIN)) (PreH13 : (0 <= ((string_length (input)) + 1 ))) (PreH14 : (start >= 0)) (PreH15 : (i >= n)) (PreH16 : (i <= n)) (PreH17 : (0 <= i)) (PreH18 : (i <= (n + 1 ))) (PreH19 : (n = (string_length (input)))) (PreH20 : (0 <= output_size)) (PreH21 : (output_size <= i)) (PreH22 : (output_size = (Zlength (output_words)))) (PreH23 : (output_size = (Zlength (output_ptrs)))) (PreH24 : (cap = (n + 1 ))) (PreH25 : (0 <= cap)) (PreH26 : (cap < INT_MAX)) (PreH27 : (output_size <= cap)) (PreH28 : (out <> 0)) (PreH29 : (data <> 0)) (PreH30 : (split_prefix_state_101 input i start output_words )) (PreH31 : (problem_101_pre_z input )) (PreH32 : (valid_string input )) (PreH33 : ((2 * ((string_length (input)) + 1 ) ) < INT_MAX)) ,
  (CharArray.full input_ptr ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "w" ) )) # Ptr  |->_)
  **  ((( &( "len" ) )) # Int  |-> (i - start ))
  **  ((( &( "ch" ) )) # Char  |-> 32)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "s" ) )) # Ptr  |-> input_ptr)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size cap )
  **  (words_rows_heap_101 output_ptrs output_words )
|--
  “ (0 < ((i - start ) + 1 )) ”
.

Definition words_string_partial_solve_wit_4_aux := 
forall (input_ptr: Z) (input: (@list Z)) (start: Z) (data: Z) (out: Z) (cap: Z) (output_ptrs: (@list Z)) (output_words: (@list (@list Z))) (output_size: Z) (n: Z) (i: Z) (PreH1 : (start >= 0)) (PreH2 : (i >= n)) (PreH3 : (i <= n)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n + 1 ))) (PreH6 : (n = (string_length (input)))) (PreH7 : (0 <= output_size)) (PreH8 : (output_size <= i)) (PreH9 : (output_size = (Zlength (output_words)))) (PreH10 : (output_size = (Zlength (output_ptrs)))) (PreH11 : (cap = (n + 1 ))) (PreH12 : (0 <= cap)) (PreH13 : (cap < INT_MAX)) (PreH14 : (output_size <= cap)) (PreH15 : (out <> 0)) (PreH16 : (data <> 0)) (PreH17 : (split_prefix_state_101 input i start output_words )) (PreH18 : (problem_101_pre_z input )) (PreH19 : (valid_string input )) (PreH20 : ((2 * ((string_length (input)) + 1 ) ) < INT_MAX)) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (store_string input_ptr input )
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size cap )
  **  (words_rows_heap_101 output_ptrs output_words )
|--
  “ (((i - start ) + 1 ) < INT_MAX) ” 
  &&  “ (0 < ((i - start ) + 1 )) ” 
  &&  “ (0 <= ((string_length (input)) + 1 )) ” 
  &&  “ (start >= 0) ” 
  &&  “ (i >= n) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (n + 1 )) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= i) ” 
  &&  “ (output_size = (Zlength (output_words))) ” 
  &&  “ (output_size = (Zlength (output_ptrs))) ” 
  &&  “ (cap = (n + 1 )) ” 
  &&  “ (0 <= cap) ” 
  &&  “ (cap < INT_MAX) ” 
  &&  “ (output_size <= cap) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (split_prefix_state_101 input i start output_words ) ” 
  &&  “ (problem_101_pre_z input ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ ((2 * ((string_length (input)) + 1 ) ) < INT_MAX) ”
  &&  (CharArray.full input_ptr ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size cap )
  **  (words_rows_heap_101 output_ptrs output_words )
.

Definition words_string_partial_solve_wit_4 := words_string_partial_solve_wit_4_pure -> words_string_partial_solve_wit_4_aux.

Definition words_string_partial_solve_wit_5_pure := 
(
forall (input_ptr: Z) (input: (@list Z)) (start: Z) (data: Z) (out: Z) (cap: Z) (output_ptrs: (@list Z)) (output_words: (@list (@list Z))) (output_size: Z) (n: Z) (i: Z) (PreH1 : (start >= 0)) (PreH2 : ((Znth i (c_string (input)) 0) = 32)) (PreH3 : (i < n)) (PreH4 : (i <= n)) (PreH5 : (0 <= i)) (PreH6 : (i <= (n + 1 ))) (PreH7 : (n = (string_length (input)))) (PreH8 : (0 <= output_size)) (PreH9 : (output_size <= i)) (PreH10 : (output_size = (Zlength (output_words)))) (PreH11 : (output_size = (Zlength (output_ptrs)))) (PreH12 : (cap = (n + 1 ))) (PreH13 : (0 <= cap)) (PreH14 : (cap < INT_MAX)) (PreH15 : (output_size <= cap)) (PreH16 : (out <> 0)) (PreH17 : (data <> 0)) (PreH18 : (split_prefix_state_101 input i start output_words )) (PreH19 : (problem_101_pre_z input )) (PreH20 : (valid_string input )) (PreH21 : ((2 * ((string_length (input)) + 1 ) ) < INT_MAX)) ,
  ((( &( "w" ) )) # Ptr  |->_)
  **  ((( &( "len" ) )) # Int  |-> (i - start ))
  **  ((( &( "ch" ) )) # Char  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "s" ) )) # Ptr  |-> input_ptr)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (store_string input_ptr input )
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size cap )
  **  (words_rows_heap_101 output_ptrs output_words )
|--
  “ (((i - start ) + 1 ) < INT_MAX) ” 
  &&  “ (0 < ((i - start ) + 1 )) ”
) \/
(
forall (input_ptr: Z) (input: (@list Z)) (start: Z) (data: Z) (out: Z) (cap: Z) (output_ptrs: (@list Z)) (output_words: (@list (@list Z))) (output_size: Z) (n: Z) (i: Z) (PreH1 : (start <= INT_MAX)) (PreH2 : (cap <= INT_MAX)) (PreH3 : (output_size <= INT_MAX)) (PreH4 : (n <= INT_MAX)) (PreH5 : (i <= INT_MAX)) (PreH6 : ((i - start ) <= INT_MAX)) (PreH7 : (start >= INT_MIN)) (PreH8 : (cap >= INT_MIN)) (PreH9 : (output_size >= INT_MIN)) (PreH10 : (n >= INT_MIN)) (PreH11 : (i >= INT_MIN)) (PreH12 : ((i - start ) >= INT_MIN)) (PreH13 : (0 <= ((string_length (input)) + 1 ))) (PreH14 : (start >= 0)) (PreH15 : ((Znth i (c_string (input)) 0) = 32)) (PreH16 : (i < n)) (PreH17 : (i <= n)) (PreH18 : (0 <= i)) (PreH19 : (i <= (n + 1 ))) (PreH20 : (n = (string_length (input)))) (PreH21 : (0 <= output_size)) (PreH22 : (output_size <= i)) (PreH23 : (output_size = (Zlength (output_words)))) (PreH24 : (output_size = (Zlength (output_ptrs)))) (PreH25 : (cap = (n + 1 ))) (PreH26 : (0 <= cap)) (PreH27 : (cap < INT_MAX)) (PreH28 : (output_size <= cap)) (PreH29 : (out <> 0)) (PreH30 : (data <> 0)) (PreH31 : (split_prefix_state_101 input i start output_words )) (PreH32 : (problem_101_pre_z input )) (PreH33 : (valid_string input )) (PreH34 : ((2 * ((string_length (input)) + 1 ) ) < INT_MAX)) ,
  (CharArray.full input_ptr ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "w" ) )) # Ptr  |->_)
  **  ((( &( "len" ) )) # Int  |-> (i - start ))
  **  ((( &( "ch" ) )) # Char  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "s" ) )) # Ptr  |-> input_ptr)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size cap )
  **  (words_rows_heap_101 output_ptrs output_words )
|--
  “ (0 < ((i - start ) + 1 )) ”
).

Definition words_string_partial_solve_wit_5_pure_split_goal_1 := 
forall (input_ptr: Z) (input: (@list Z)) (start: Z) (data: Z) (out: Z) (cap: Z) (output_ptrs: (@list Z)) (output_words: (@list (@list Z))) (output_size: Z) (n: Z) (i: Z) (PreH1 : (start <= INT_MAX)) (PreH2 : (cap <= INT_MAX)) (PreH3 : (output_size <= INT_MAX)) (PreH4 : (n <= INT_MAX)) (PreH5 : (i <= INT_MAX)) (PreH6 : ((i - start ) <= INT_MAX)) (PreH7 : (start >= INT_MIN)) (PreH8 : (cap >= INT_MIN)) (PreH9 : (output_size >= INT_MIN)) (PreH10 : (n >= INT_MIN)) (PreH11 : (i >= INT_MIN)) (PreH12 : ((i - start ) >= INT_MIN)) (PreH13 : (0 <= ((string_length (input)) + 1 ))) (PreH14 : (start >= 0)) (PreH15 : ((Znth i (c_string (input)) 0) = 32)) (PreH16 : (i < n)) (PreH17 : (i <= n)) (PreH18 : (0 <= i)) (PreH19 : (i <= (n + 1 ))) (PreH20 : (n = (string_length (input)))) (PreH21 : (0 <= output_size)) (PreH22 : (output_size <= i)) (PreH23 : (output_size = (Zlength (output_words)))) (PreH24 : (output_size = (Zlength (output_ptrs)))) (PreH25 : (cap = (n + 1 ))) (PreH26 : (0 <= cap)) (PreH27 : (cap < INT_MAX)) (PreH28 : (output_size <= cap)) (PreH29 : (out <> 0)) (PreH30 : (data <> 0)) (PreH31 : (split_prefix_state_101 input i start output_words )) (PreH32 : (problem_101_pre_z input )) (PreH33 : (valid_string input )) (PreH34 : ((2 * ((string_length (input)) + 1 ) ) < INT_MAX)) ,
  (CharArray.full input_ptr ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "w" ) )) # Ptr  |->_)
  **  ((( &( "len" ) )) # Int  |-> (i - start ))
  **  ((( &( "ch" ) )) # Char  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "s" ) )) # Ptr  |-> input_ptr)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size cap )
  **  (words_rows_heap_101 output_ptrs output_words )
|--
  “ (0 < ((i - start ) + 1 )) ”
.

Definition words_string_partial_solve_wit_5_aux := 
forall (input_ptr: Z) (input: (@list Z)) (start: Z) (data: Z) (out: Z) (cap: Z) (output_ptrs: (@list Z)) (output_words: (@list (@list Z))) (output_size: Z) (n: Z) (i: Z) (PreH1 : (start >= 0)) (PreH2 : ((Znth i (c_string (input)) 0) = 32)) (PreH3 : (i < n)) (PreH4 : (i <= n)) (PreH5 : (0 <= i)) (PreH6 : (i <= (n + 1 ))) (PreH7 : (n = (string_length (input)))) (PreH8 : (0 <= output_size)) (PreH9 : (output_size <= i)) (PreH10 : (output_size = (Zlength (output_words)))) (PreH11 : (output_size = (Zlength (output_ptrs)))) (PreH12 : (cap = (n + 1 ))) (PreH13 : (0 <= cap)) (PreH14 : (cap < INT_MAX)) (PreH15 : (output_size <= cap)) (PreH16 : (out <> 0)) (PreH17 : (data <> 0)) (PreH18 : (split_prefix_state_101 input i start output_words )) (PreH19 : (problem_101_pre_z input )) (PreH20 : (valid_string input )) (PreH21 : ((2 * ((string_length (input)) + 1 ) ) < INT_MAX)) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (store_string input_ptr input )
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size cap )
  **  (words_rows_heap_101 output_ptrs output_words )
|--
  “ (((i - start ) + 1 ) < INT_MAX) ” 
  &&  “ (0 < ((i - start ) + 1 )) ” 
  &&  “ (0 <= ((string_length (input)) + 1 )) ” 
  &&  “ (start >= 0) ” 
  &&  “ ((Znth i (c_string (input)) 0) = 32) ” 
  &&  “ (i < n) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (n + 1 )) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= i) ” 
  &&  “ (output_size = (Zlength (output_words))) ” 
  &&  “ (output_size = (Zlength (output_ptrs))) ” 
  &&  “ (cap = (n + 1 )) ” 
  &&  “ (0 <= cap) ” 
  &&  “ (cap < INT_MAX) ” 
  &&  “ (output_size <= cap) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (split_prefix_state_101 input i start output_words ) ” 
  &&  “ (problem_101_pre_z input ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ ((2 * ((string_length (input)) + 1 ) ) < INT_MAX) ”
  &&  (CharArray.full input_ptr ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size cap )
  **  (words_rows_heap_101 output_ptrs output_words )
.

Definition words_string_partial_solve_wit_5 := words_string_partial_solve_wit_5_pure -> words_string_partial_solve_wit_5_aux.

Definition words_string_partial_solve_wit_6_pure := 
(
forall (input_ptr: Z) (input: (@list Z)) (start: Z) (data: Z) (out: Z) (cap: Z) (output_ptrs: (@list Z)) (output_words: (@list (@list Z))) (output_size: Z) (n: Z) (i: Z) (PreH1 : (start >= 0)) (PreH2 : ((Znth i (c_string (input)) 0) = 44)) (PreH3 : ((Znth i (c_string (input)) 0) <> 32)) (PreH4 : (i < n)) (PreH5 : (i <= n)) (PreH6 : (0 <= i)) (PreH7 : (i <= (n + 1 ))) (PreH8 : (n = (string_length (input)))) (PreH9 : (0 <= output_size)) (PreH10 : (output_size <= i)) (PreH11 : (output_size = (Zlength (output_words)))) (PreH12 : (output_size = (Zlength (output_ptrs)))) (PreH13 : (cap = (n + 1 ))) (PreH14 : (0 <= cap)) (PreH15 : (cap < INT_MAX)) (PreH16 : (output_size <= cap)) (PreH17 : (out <> 0)) (PreH18 : (data <> 0)) (PreH19 : (split_prefix_state_101 input i start output_words )) (PreH20 : (problem_101_pre_z input )) (PreH21 : (valid_string input )) (PreH22 : ((2 * ((string_length (input)) + 1 ) ) < INT_MAX)) ,
  ((( &( "w" ) )) # Ptr  |->_)
  **  ((( &( "len" ) )) # Int  |-> (i - start ))
  **  ((( &( "ch" ) )) # Char  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "s" ) )) # Ptr  |-> input_ptr)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (store_string input_ptr input )
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size cap )
  **  (words_rows_heap_101 output_ptrs output_words )
|--
  “ (((i - start ) + 1 ) < INT_MAX) ” 
  &&  “ (0 < ((i - start ) + 1 )) ”
) \/
(
forall (input_ptr: Z) (input: (@list Z)) (start: Z) (data: Z) (out: Z) (cap: Z) (output_ptrs: (@list Z)) (output_words: (@list (@list Z))) (output_size: Z) (n: Z) (i: Z) (PreH1 : (start <= INT_MAX)) (PreH2 : (cap <= INT_MAX)) (PreH3 : (output_size <= INT_MAX)) (PreH4 : (n <= INT_MAX)) (PreH5 : (i <= INT_MAX)) (PreH6 : ((i - start ) <= INT_MAX)) (PreH7 : (start >= INT_MIN)) (PreH8 : (cap >= INT_MIN)) (PreH9 : (output_size >= INT_MIN)) (PreH10 : (n >= INT_MIN)) (PreH11 : (i >= INT_MIN)) (PreH12 : ((i - start ) >= INT_MIN)) (PreH13 : (0 <= ((string_length (input)) + 1 ))) (PreH14 : (start >= 0)) (PreH15 : ((Znth i (c_string (input)) 0) = 44)) (PreH16 : ((Znth i (c_string (input)) 0) <> 32)) (PreH17 : (i < n)) (PreH18 : (i <= n)) (PreH19 : (0 <= i)) (PreH20 : (i <= (n + 1 ))) (PreH21 : (n = (string_length (input)))) (PreH22 : (0 <= output_size)) (PreH23 : (output_size <= i)) (PreH24 : (output_size = (Zlength (output_words)))) (PreH25 : (output_size = (Zlength (output_ptrs)))) (PreH26 : (cap = (n + 1 ))) (PreH27 : (0 <= cap)) (PreH28 : (cap < INT_MAX)) (PreH29 : (output_size <= cap)) (PreH30 : (out <> 0)) (PreH31 : (data <> 0)) (PreH32 : (split_prefix_state_101 input i start output_words )) (PreH33 : (problem_101_pre_z input )) (PreH34 : (valid_string input )) (PreH35 : ((2 * ((string_length (input)) + 1 ) ) < INT_MAX)) ,
  (CharArray.full input_ptr ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "w" ) )) # Ptr  |->_)
  **  ((( &( "len" ) )) # Int  |-> (i - start ))
  **  ((( &( "ch" ) )) # Char  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "s" ) )) # Ptr  |-> input_ptr)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size cap )
  **  (words_rows_heap_101 output_ptrs output_words )
|--
  “ (0 < ((i - start ) + 1 )) ”
).

Definition words_string_partial_solve_wit_6_pure_split_goal_1 := 
forall (input_ptr: Z) (input: (@list Z)) (start: Z) (data: Z) (out: Z) (cap: Z) (output_ptrs: (@list Z)) (output_words: (@list (@list Z))) (output_size: Z) (n: Z) (i: Z) (PreH1 : (start <= INT_MAX)) (PreH2 : (cap <= INT_MAX)) (PreH3 : (output_size <= INT_MAX)) (PreH4 : (n <= INT_MAX)) (PreH5 : (i <= INT_MAX)) (PreH6 : ((i - start ) <= INT_MAX)) (PreH7 : (start >= INT_MIN)) (PreH8 : (cap >= INT_MIN)) (PreH9 : (output_size >= INT_MIN)) (PreH10 : (n >= INT_MIN)) (PreH11 : (i >= INT_MIN)) (PreH12 : ((i - start ) >= INT_MIN)) (PreH13 : (0 <= ((string_length (input)) + 1 ))) (PreH14 : (start >= 0)) (PreH15 : ((Znth i (c_string (input)) 0) = 44)) (PreH16 : ((Znth i (c_string (input)) 0) <> 32)) (PreH17 : (i < n)) (PreH18 : (i <= n)) (PreH19 : (0 <= i)) (PreH20 : (i <= (n + 1 ))) (PreH21 : (n = (string_length (input)))) (PreH22 : (0 <= output_size)) (PreH23 : (output_size <= i)) (PreH24 : (output_size = (Zlength (output_words)))) (PreH25 : (output_size = (Zlength (output_ptrs)))) (PreH26 : (cap = (n + 1 ))) (PreH27 : (0 <= cap)) (PreH28 : (cap < INT_MAX)) (PreH29 : (output_size <= cap)) (PreH30 : (out <> 0)) (PreH31 : (data <> 0)) (PreH32 : (split_prefix_state_101 input i start output_words )) (PreH33 : (problem_101_pre_z input )) (PreH34 : (valid_string input )) (PreH35 : ((2 * ((string_length (input)) + 1 ) ) < INT_MAX)) ,
  (CharArray.full input_ptr ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "w" ) )) # Ptr  |->_)
  **  ((( &( "len" ) )) # Int  |-> (i - start ))
  **  ((( &( "ch" ) )) # Char  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "s" ) )) # Ptr  |-> input_ptr)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size cap )
  **  (words_rows_heap_101 output_ptrs output_words )
|--
  “ (0 < ((i - start ) + 1 )) ”
.

Definition words_string_partial_solve_wit_6_aux := 
forall (input_ptr: Z) (input: (@list Z)) (start: Z) (data: Z) (out: Z) (cap: Z) (output_ptrs: (@list Z)) (output_words: (@list (@list Z))) (output_size: Z) (n: Z) (i: Z) (PreH1 : (start >= 0)) (PreH2 : ((Znth i (c_string (input)) 0) = 44)) (PreH3 : ((Znth i (c_string (input)) 0) <> 32)) (PreH4 : (i < n)) (PreH5 : (i <= n)) (PreH6 : (0 <= i)) (PreH7 : (i <= (n + 1 ))) (PreH8 : (n = (string_length (input)))) (PreH9 : (0 <= output_size)) (PreH10 : (output_size <= i)) (PreH11 : (output_size = (Zlength (output_words)))) (PreH12 : (output_size = (Zlength (output_ptrs)))) (PreH13 : (cap = (n + 1 ))) (PreH14 : (0 <= cap)) (PreH15 : (cap < INT_MAX)) (PreH16 : (output_size <= cap)) (PreH17 : (out <> 0)) (PreH18 : (data <> 0)) (PreH19 : (split_prefix_state_101 input i start output_words )) (PreH20 : (problem_101_pre_z input )) (PreH21 : (valid_string input )) (PreH22 : ((2 * ((string_length (input)) + 1 ) ) < INT_MAX)) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (store_string input_ptr input )
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size cap )
  **  (words_rows_heap_101 output_ptrs output_words )
|--
  “ (((i - start ) + 1 ) < INT_MAX) ” 
  &&  “ (0 < ((i - start ) + 1 )) ” 
  &&  “ (0 <= ((string_length (input)) + 1 )) ” 
  &&  “ (start >= 0) ” 
  &&  “ ((Znth i (c_string (input)) 0) = 44) ” 
  &&  “ ((Znth i (c_string (input)) 0) <> 32) ” 
  &&  “ (i < n) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (n + 1 )) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= i) ” 
  &&  “ (output_size = (Zlength (output_words))) ” 
  &&  “ (output_size = (Zlength (output_ptrs))) ” 
  &&  “ (cap = (n + 1 )) ” 
  &&  “ (0 <= cap) ” 
  &&  “ (cap < INT_MAX) ” 
  &&  “ (output_size <= cap) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (split_prefix_state_101 input i start output_words ) ” 
  &&  “ (problem_101_pre_z input ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ ((2 * ((string_length (input)) + 1 ) ) < INT_MAX) ”
  &&  (CharArray.full input_ptr ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size cap )
  **  (words_rows_heap_101 output_ptrs output_words )
.

Definition words_string_partial_solve_wit_6 := words_string_partial_solve_wit_6_pure -> words_string_partial_solve_wit_6_aux.

Definition words_string_partial_solve_wit_7_pure := 
forall (input_ptr: Z) (input: (@list Z)) (input_pre: (@list Z)) (input_post: (@list Z)) (output_words: (@list (@list Z))) (output_ptrs: (@list Z)) (start: Z) (i: Z) (n: Z) (len: Z) (output_size: Z) (cap: Z) (out: Z) (data: Z) (w: Z) (ch: Z) (PreH1 : (0 <= start)) (PreH2 : (start < i)) (PreH3 : (i <= n)) (PreH4 : (len = (i - start ))) (PreH5 : ((Zlength ((sublist (start) (i) (input)))) = len)) (PreH6 : (all_ascii (sublist (start) (i) (input)) )) (PreH7 : (input_pre = (sublist (0) (start) ((c_string (input)))))) (PreH8 : (input_post = (sublist (i) ((n + 1 )) ((c_string (input)))))) (PreH9 : (n = (string_length (input)))) (PreH10 : (0 <= output_size)) (PreH11 : (output_size <= i)) (PreH12 : (output_size = (Zlength (output_words)))) (PreH13 : (output_size = (Zlength (output_ptrs)))) (PreH14 : (output_size <= cap)) (PreH15 : (cap = (n + 1 ))) (PreH16 : (0 <= cap)) (PreH17 : (cap < INT_MAX)) (PreH18 : (out <> 0)) (PreH19 : (data <> 0)) (PreH20 : (w <> 0)) (PreH21 : (closing_delimiter_101 input i n )) (PreH22 : (split_prefix_state_101 input i start output_words )) (PreH23 : (problem_101_pre_z input )) (PreH24 : (valid_string input )) (PreH25 : ((2 * ((string_length (input)) + 1 ) ) < INT_MAX)) ,
  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "ch" ) )) # Char  |-> ch)
  **  ((( &( "s" ) )) # Ptr  |-> input_ptr)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (CharArray.seg input_ptr 0 start input_pre )
  **  (CharArray.full (input_ptr + (start * sizeof(CHAR) ) ) len (sublist (start) (i) (input)) )
  **  (CharArray.seg input_ptr i (n + 1 ) input_post )
  **  (CharArray.undef_full w len )
  **  (CharArray.undef_seg w len (len + 1 ) )
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size cap )
  **  (words_rows_heap_101 output_ptrs output_words )
|--
  “ (all_ascii (sublist (start) (i) (input)) ) ” 
  &&  “ ((Zlength ((sublist (start) (i) (input)))) = len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ”
.

Definition words_string_partial_solve_wit_7_aux := 
forall (input_ptr: Z) (input: (@list Z)) (input_pre: (@list Z)) (input_post: (@list Z)) (output_words: (@list (@list Z))) (output_ptrs: (@list Z)) (start: Z) (i: Z) (n: Z) (len: Z) (output_size: Z) (cap: Z) (out: Z) (data: Z) (w: Z) (PreH1 : (0 <= start)) (PreH2 : (start < i)) (PreH3 : (i <= n)) (PreH4 : (len = (i - start ))) (PreH5 : ((Zlength ((sublist (start) (i) (input)))) = len)) (PreH6 : (all_ascii (sublist (start) (i) (input)) )) (PreH7 : (input_pre = (sublist (0) (start) ((c_string (input)))))) (PreH8 : (input_post = (sublist (i) ((n + 1 )) ((c_string (input)))))) (PreH9 : (n = (string_length (input)))) (PreH10 : (0 <= output_size)) (PreH11 : (output_size <= i)) (PreH12 : (output_size = (Zlength (output_words)))) (PreH13 : (output_size = (Zlength (output_ptrs)))) (PreH14 : (output_size <= cap)) (PreH15 : (cap = (n + 1 ))) (PreH16 : (0 <= cap)) (PreH17 : (cap < INT_MAX)) (PreH18 : (out <> 0)) (PreH19 : (data <> 0)) (PreH20 : (w <> 0)) (PreH21 : (closing_delimiter_101 input i n )) (PreH22 : (split_prefix_state_101 input i start output_words )) (PreH23 : (problem_101_pre_z input )) (PreH24 : (valid_string input )) (PreH25 : ((2 * ((string_length (input)) + 1 ) ) < INT_MAX)) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (CharArray.seg input_ptr 0 start input_pre )
  **  (CharArray.full (input_ptr + (start * sizeof(CHAR) ) ) len (sublist (start) (i) (input)) )
  **  (CharArray.seg input_ptr i (n + 1 ) input_post )
  **  (CharArray.undef_full w len )
  **  (CharArray.undef_seg w len (len + 1 ) )
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size cap )
  **  (words_rows_heap_101 output_ptrs output_words )
|--
  “ (all_ascii (sublist (start) (i) (input)) ) ” 
  &&  “ ((Zlength ((sublist (start) (i) (input)))) = len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (0 <= start) ” 
  &&  “ (start < i) ” 
  &&  “ (i <= n) ” 
  &&  “ (len = (i - start )) ” 
  &&  “ ((Zlength ((sublist (start) (i) (input)))) = len) ” 
  &&  “ (all_ascii (sublist (start) (i) (input)) ) ” 
  &&  “ (input_pre = (sublist (0) (start) ((c_string (input))))) ” 
  &&  “ (input_post = (sublist (i) ((n + 1 )) ((c_string (input))))) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= i) ” 
  &&  “ (output_size = (Zlength (output_words))) ” 
  &&  “ (output_size = (Zlength (output_ptrs))) ” 
  &&  “ (output_size <= cap) ” 
  &&  “ (cap = (n + 1 )) ” 
  &&  “ (0 <= cap) ” 
  &&  “ (cap < INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (w <> 0) ” 
  &&  “ (closing_delimiter_101 input i n ) ” 
  &&  “ (split_prefix_state_101 input i start output_words ) ” 
  &&  “ (problem_101_pre_z input ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ ((2 * ((string_length (input)) + 1 ) ) < INT_MAX) ”
  &&  (CharArray.undef_full w len )
  **  (CharArray.full (input_ptr + (start * sizeof(CHAR) ) ) len (sublist (start) (i) (input)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (CharArray.seg input_ptr 0 start input_pre )
  **  (CharArray.seg input_ptr i (n + 1 ) input_post )
  **  (CharArray.undef_seg w len (len + 1 ) )
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size cap )
  **  (words_rows_heap_101 output_ptrs output_words )
.

Definition words_string_partial_solve_wit_7 := words_string_partial_solve_wit_7_pure -> words_string_partial_solve_wit_7_aux.

Definition words_string_partial_solve_wit_8 := 
forall (input_ptr: Z) (input: (@list Z)) (input_pre: (@list Z)) (input_post: (@list Z)) (output_words: (@list (@list Z))) (output_ptrs: (@list Z)) (start: Z) (i: Z) (n: Z) (len: Z) (output_size: Z) (cap: Z) (out: Z) (data: Z) (w: Z) (retval: Z) (PreH1 : (retval = w)) (PreH2 : (0 <= start)) (PreH3 : (start < i)) (PreH4 : (i <= n)) (PreH5 : (len = (i - start ))) (PreH6 : ((Zlength ((sublist (start) (i) (input)))) = len)) (PreH7 : (all_ascii (sublist (start) (i) (input)) )) (PreH8 : (input_pre = (sublist (0) (start) ((c_string (input)))))) (PreH9 : (input_post = (sublist (i) ((n + 1 )) ((c_string (input)))))) (PreH10 : (n = (string_length (input)))) (PreH11 : (0 <= output_size)) (PreH12 : (output_size <= i)) (PreH13 : (output_size = (Zlength (output_words)))) (PreH14 : (output_size = (Zlength (output_ptrs)))) (PreH15 : (output_size <= cap)) (PreH16 : (cap = (n + 1 ))) (PreH17 : (0 <= cap)) (PreH18 : (cap < INT_MAX)) (PreH19 : (out <> 0)) (PreH20 : (data <> 0)) (PreH21 : (w <> 0)) (PreH22 : (closing_delimiter_101 input i n )) (PreH23 : (split_prefix_state_101 input i start output_words )) (PreH24 : (problem_101_pre_z input )) (PreH25 : (valid_string input )) (PreH26 : ((2 * ((string_length (input)) + 1 ) ) < INT_MAX)) ,
  (CharArray.full w len (sublist (start) (i) (input)) )
  **  (CharArray.full (input_ptr + (start * sizeof(CHAR) ) ) len (sublist (start) (i) (input)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (CharArray.seg input_ptr 0 start input_pre )
  **  (CharArray.seg input_ptr i (n + 1 ) input_post )
  **  (CharArray.undef_seg w len (len + 1 ) )
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size cap )
  **  (words_rows_heap_101 output_ptrs output_words )
|--
  “ (0 <= len) ” 
  &&  “ (retval = w) ” 
  &&  “ (0 <= start) ” 
  &&  “ (start < i) ” 
  &&  “ (i <= n) ” 
  &&  “ (len = (i - start )) ” 
  &&  “ ((Zlength ((sublist (start) (i) (input)))) = len) ” 
  &&  “ (all_ascii (sublist (start) (i) (input)) ) ” 
  &&  “ (input_pre = (sublist (0) (start) ((c_string (input))))) ” 
  &&  “ (input_post = (sublist (i) ((n + 1 )) ((c_string (input))))) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= i) ” 
  &&  “ (output_size = (Zlength (output_words))) ” 
  &&  “ (output_size = (Zlength (output_ptrs))) ” 
  &&  “ (output_size <= cap) ” 
  &&  “ (cap = (n + 1 )) ” 
  &&  “ (0 <= cap) ” 
  &&  “ (cap < INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (w <> 0) ” 
  &&  “ (closing_delimiter_101 input i n ) ” 
  &&  “ (split_prefix_state_101 input i start output_words ) ” 
  &&  “ (problem_101_pre_z input ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ ((2 * ((string_length (input)) + 1 ) ) < INT_MAX) ”
  &&  (((w + (len * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i w len len (len + 1 ) )
  **  (CharArray.full w len (sublist (start) (i) (input)) )
  **  (CharArray.full (input_ptr + (start * sizeof(CHAR) ) ) len (sublist (start) (i) (input)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (CharArray.seg input_ptr 0 start input_pre )
  **  (CharArray.seg input_ptr i (n + 1 ) input_post )
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size cap )
  **  (words_rows_heap_101 output_ptrs output_words )
.

Definition words_string_partial_solve_wit_9 := 
forall (input_ptr: Z) (input: (@list Z)) (output_words: (@list (@list Z))) (output_ptrs: (@list Z)) (start: Z) (i: Z) (n: Z) (len: Z) (output_size: Z) (cap: Z) (out: Z) (data: Z) (w: Z) (PreH1 : (0 <= start)) (PreH2 : (start < i)) (PreH3 : (i <= n)) (PreH4 : (len = (i - start ))) (PreH5 : (n = (string_length (input)))) (PreH6 : (0 <= output_size)) (PreH7 : (output_size <= i)) (PreH8 : (output_size = (Zlength (output_words)))) (PreH9 : (output_size = (Zlength (output_ptrs)))) (PreH10 : (output_size < cap)) (PreH11 : (cap = (n + 1 ))) (PreH12 : (0 <= cap)) (PreH13 : (cap < INT_MAX)) (PreH14 : (out <> 0)) (PreH15 : (data <> 0)) (PreH16 : (w <> 0)) (PreH17 : (closing_delimiter_101 input i n )) (PreH18 : (split_prefix_state_101 input i start output_words )) (PreH19 : (problem_101_pre_z input )) (PreH20 : (valid_string input )) (PreH21 : ((2 * ((string_length (input)) + 1 ) ) < INT_MAX)) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (store_string input_ptr input )
  **  (CharArray.full w (Zlength ((c_string ((sublist (start) (i) (input)))))) (c_string ((sublist (start) (i) (input)))) )
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size cap )
  **  (words_rows_heap_101 output_ptrs output_words )
|--
  “ (0 <= ((string_length (input)) + 1 )) ” 
  &&  “ (0 <= (Zlength ((c_string ((sublist (start) (i) (input))))))) ” 
  &&  “ (0 <= start) ” 
  &&  “ (start < i) ” 
  &&  “ (i <= n) ” 
  &&  “ (len = (i - start )) ” 
  &&  “ (n = (string_length (input))) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= i) ” 
  &&  “ (output_size = (Zlength (output_words))) ” 
  &&  “ (output_size = (Zlength (output_ptrs))) ” 
  &&  “ (output_size < cap) ” 
  &&  “ (cap = (n + 1 )) ” 
  &&  “ (0 <= cap) ” 
  &&  “ (cap < INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (w <> 0) ” 
  &&  “ (closing_delimiter_101 input i n ) ” 
  &&  “ (split_prefix_state_101 input i start output_words ) ” 
  &&  “ (problem_101_pre_z input ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ ((2 * ((string_length (input)) + 1 ) ) < INT_MAX) ”
  &&  (((data + (output_size * sizeof(PTR) ) )) # Ptr  |->_)
  **  (PtrArray.undef_seg data (output_size + 1 ) cap )
  **  (CharArray.full input_ptr ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (CharArray.full w (Zlength ((c_string ((sublist (start) (i) (input)))))) (c_string ((sublist (start) (i) (input)))) )
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (words_rows_heap_101 output_ptrs output_words )
.

Module Type VC_Correct.

Include ptr_array2_Strategy_Correct.
Include char_array_Strategy_Correct.
Include string_Strategy_Correct.

Axiom proof_of_words_string_safety_wit_1 : words_string_safety_wit_1.
Axiom proof_of_words_string_safety_wit_2 : words_string_safety_wit_2.
Axiom proof_of_words_string_safety_wit_3 : words_string_safety_wit_3.
Axiom proof_of_words_string_safety_wit_4 : words_string_safety_wit_4.
Axiom proof_of_words_string_safety_wit_5 : words_string_safety_wit_5.
Axiom proof_of_words_string_safety_wit_6 : words_string_safety_wit_6.
Axiom proof_of_words_string_safety_wit_7 : words_string_safety_wit_7.
Axiom proof_of_words_string_safety_wit_8 : words_string_safety_wit_8.
Axiom proof_of_words_string_safety_wit_9 : words_string_safety_wit_9.
Axiom proof_of_words_string_safety_wit_10 : words_string_safety_wit_10.
Axiom proof_of_words_string_safety_wit_11 : words_string_safety_wit_11.
Axiom proof_of_words_string_safety_wit_12 : words_string_safety_wit_12.
Axiom proof_of_words_string_safety_wit_13 : words_string_safety_wit_13.
Axiom proof_of_words_string_safety_wit_14 : words_string_safety_wit_14.
Axiom proof_of_words_string_safety_wit_15 : words_string_safety_wit_15.
Axiom proof_of_words_string_safety_wit_16 : words_string_safety_wit_16.
Axiom proof_of_words_string_safety_wit_17 : words_string_safety_wit_17.
Axiom proof_of_words_string_safety_wit_18 : words_string_safety_wit_18.
Axiom proof_of_words_string_safety_wit_19 : words_string_safety_wit_19.
Axiom proof_of_words_string_safety_wit_20 : words_string_safety_wit_20.
Axiom proof_of_words_string_safety_wit_21 : words_string_safety_wit_21.
Axiom proof_of_words_string_safety_wit_22 : words_string_safety_wit_22.
Axiom proof_of_words_string_safety_wit_23 : words_string_safety_wit_23.
Axiom proof_of_words_string_safety_wit_24 : words_string_safety_wit_24.
Axiom proof_of_words_string_safety_wit_25 : words_string_safety_wit_25.
Axiom proof_of_words_string_safety_wit_26 : words_string_safety_wit_26.
Axiom proof_of_words_string_safety_wit_27 : words_string_safety_wit_27.
Axiom proof_of_words_string_safety_wit_28 : words_string_safety_wit_28.
Axiom proof_of_words_string_safety_wit_29 : words_string_safety_wit_29.
Axiom proof_of_words_string_safety_wit_30 : words_string_safety_wit_30.
Axiom proof_of_words_string_safety_wit_31 : words_string_safety_wit_31.
Axiom proof_of_words_string_safety_wit_32 : words_string_safety_wit_32.
Axiom proof_of_words_string_safety_wit_33 : words_string_safety_wit_33.
Axiom proof_of_words_string_safety_wit_34 : words_string_safety_wit_34.
Axiom proof_of_words_string_entail_wit_1 : words_string_entail_wit_1.
Axiom proof_of_words_string_entail_wit_2_1 : words_string_entail_wit_2_1.
Axiom proof_of_words_string_entail_wit_2_2 : words_string_entail_wit_2_2.
Axiom proof_of_words_string_entail_wit_2_3 : words_string_entail_wit_2_3.
Axiom proof_of_words_string_entail_wit_3 : words_string_entail_wit_3.
Axiom proof_of_words_string_entail_wit_4_1 : words_string_entail_wit_4_1.
Axiom proof_of_words_string_entail_wit_4_2 : words_string_entail_wit_4_2.
Axiom proof_of_words_string_entail_wit_4_3 : words_string_entail_wit_4_3.
Axiom proof_of_words_string_entail_wit_4_4 : words_string_entail_wit_4_4.
Axiom proof_of_words_string_entail_wit_4_5 : words_string_entail_wit_4_5.
Axiom proof_of_words_string_entail_wit_4_6 : words_string_entail_wit_4_6.
Axiom proof_of_words_string_return_wit_1 : words_string_return_wit_1.
Axiom proof_of_words_string_partial_solve_wit_1 : words_string_partial_solve_wit_1.
Axiom proof_of_words_string_partial_solve_wit_2_pure : words_string_partial_solve_wit_2_pure.
Axiom proof_of_words_string_partial_solve_wit_2 : words_string_partial_solve_wit_2.
Axiom proof_of_words_string_partial_solve_wit_3_pure : words_string_partial_solve_wit_3_pure.
Axiom proof_of_words_string_partial_solve_wit_3 : words_string_partial_solve_wit_3.
Axiom proof_of_words_string_partial_solve_wit_4_pure : words_string_partial_solve_wit_4_pure.
Axiom proof_of_words_string_partial_solve_wit_4 : words_string_partial_solve_wit_4.
Axiom proof_of_words_string_partial_solve_wit_5_pure : words_string_partial_solve_wit_5_pure.
Axiom proof_of_words_string_partial_solve_wit_5 : words_string_partial_solve_wit_5.
Axiom proof_of_words_string_partial_solve_wit_6_pure : words_string_partial_solve_wit_6_pure.
Axiom proof_of_words_string_partial_solve_wit_6 : words_string_partial_solve_wit_6.
Axiom proof_of_words_string_partial_solve_wit_7_pure : words_string_partial_solve_wit_7_pure.
Axiom proof_of_words_string_partial_solve_wit_7 : words_string_partial_solve_wit_7.
Axiom proof_of_words_string_partial_solve_wit_8 : words_string_partial_solve_wit_8.
Axiom proof_of_words_string_partial_solve_wit_9 : words_string_partial_solve_wit_9.

End VC_Correct.
