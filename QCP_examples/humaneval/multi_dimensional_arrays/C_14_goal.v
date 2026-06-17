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
Require Import coins_14.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import ptr_array2_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import ptr_array2_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_proof.
Require Import string_strategy_goal.
Require Import string_strategy_proof.

(*----- Function all_prefixes -----*)

Definition all_prefixes_safety_wit_1 := 
forall (str_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (str_l)))) (PreH4 : (0 <= ((string_length (str_l)) + 1 ))) (PreH5 : (valid_string str_l )) (PreH6 : (valid_prefixes_14 str_l )) (PreH7 : ((string_length (str_l)) <= 100)) (PreH8 : (problem_14_pre_z str_l )) ,
  ((( &( "cur" ) )) # Ptr  |->_)
  **  ((( &( "data" ) )) # Ptr  |-> retval_3)
  **  (PtrArray.undef_full retval_3 retval )
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_3)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> retval)
  **  (CharArray.full str_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition all_prefixes_safety_wit_2 := 
forall (str_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (str_l)))) (PreH4 : (0 <= ((string_length (str_l)) + 1 ))) (PreH5 : (valid_string str_l )) (PreH6 : (valid_prefixes_14 str_l )) (PreH7 : ((string_length (str_l)) <= 100)) (PreH8 : (problem_14_pre_z str_l )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Ptr  |-> 0)
  **  ((( &( "data" ) )) # Ptr  |-> retval_3)
  **  (PtrArray.undef_full retval_3 retval )
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_3)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> retval)
  **  (CharArray.full str_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition all_prefixes_safety_wit_3 := 
forall (str_pre: Z) (str_l: (@list Z)) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (cur: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (i < n)) (PreH2 : (0 <= i)) (PreH3 : (i <= n)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (n <= 100)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (valid_string str_l )) (PreH9 : (valid_prefixes_14 str_l )) (PreH10 : (problem_14_pre_z str_l )) (PreH11 : (prefix_rows_state_14 str_l i output_rows )) (PreH12 : ((Zlength (output_rows)) = i)) (PreH13 : ((Zlength (output_ptrs)) = i)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> n)
  **  (store_string str_pre str_l )
  **  (PtrArray.seg data 0 i output_ptrs )
  **  (PtrArray.undef_seg data i n )
  **  (prefix_rows_heap_14 output_ptrs output_rows )
|--
  “ ((i + 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 2 )) ”
.

Definition all_prefixes_safety_wit_4 := 
forall (str_pre: Z) (str_l: (@list Z)) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (cur: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (i < n)) (PreH2 : (0 <= i)) (PreH3 : (i <= n)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (n <= 100)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (valid_string str_l )) (PreH9 : (valid_prefixes_14 str_l )) (PreH10 : (problem_14_pre_z str_l )) (PreH11 : (prefix_rows_state_14 str_l i output_rows )) (PreH12 : ((Zlength (output_rows)) = i)) (PreH13 : ((Zlength (output_ptrs)) = i)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> n)
  **  (store_string str_pre str_l )
  **  (PtrArray.seg data 0 i output_ptrs )
  **  (PtrArray.undef_seg data i n )
  **  (prefix_rows_heap_14 output_ptrs output_rows )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition all_prefixes_safety_wit_5 := 
forall (str_pre: Z) (str_l: (@list Z)) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (i: Z) (n: Z) (cur: Z) (out: Z) (data: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (n <= 100)) (PreH5 : (cur <> 0)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (valid_string str_l )) (PreH9 : (valid_prefixes_14 str_l )) (PreH10 : (problem_14_pre_z str_l )) (PreH11 : (prefix_rows_state_14 str_l i output_rows )) (PreH12 : ((Zlength (output_rows)) = i)) (PreH13 : ((Zlength (output_ptrs)) = i)) (PreH14 : ((Zlength ((prefix_row_payload_14 (str_l) (i)))) = (i + 1 ))) (PreH15 : (all_ascii (prefix_row_payload_14 (str_l) (i)) )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> n)
  **  (CharArray.full str_pre (i + 1 ) (prefix_row_payload_14 (str_l) (i)) )
  **  (CharArray.seg str_pre (i + 1 ) (n + 1 ) (sublist ((i + 1 )) ((n + 1 )) ((c_string (str_l)))) )
  **  (PtrArray.seg data 0 i output_ptrs )
  **  (PtrArray.undef_seg data i n )
  **  (prefix_rows_heap_14 output_ptrs output_rows )
  **  (CharArray.undef_full cur (i + 1 ) )
  **  (CharArray.undef_seg cur (i + 1 ) (i + 2 ) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition all_prefixes_safety_wit_6 := 
forall (str_pre: Z) (str_l: (@list Z)) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (i: Z) (n: Z) (cur: Z) (out: Z) (data: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (n <= 100)) (PreH5 : (cur <> 0)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (valid_string str_l )) (PreH9 : (valid_prefixes_14 str_l )) (PreH10 : (problem_14_pre_z str_l )) (PreH11 : (prefix_rows_state_14 str_l i output_rows )) (PreH12 : ((Zlength (output_rows)) = i)) (PreH13 : ((Zlength (output_ptrs)) = i)) (PreH14 : ((Zlength ((prefix_row_payload_14 (str_l) (i)))) = (i + 1 ))) (PreH15 : (all_ascii (prefix_row_payload_14 (str_l) (i)) )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> n)
  **  (CharArray.full str_pre (i + 1 ) (prefix_row_payload_14 (str_l) (i)) )
  **  (CharArray.seg str_pre (i + 1 ) (n + 1 ) (sublist ((i + 1 )) ((n + 1 )) ((c_string (str_l)))) )
  **  (PtrArray.seg data 0 i output_ptrs )
  **  (PtrArray.undef_seg data i n )
  **  (prefix_rows_heap_14 output_ptrs output_rows )
  **  (CharArray.undef_full cur (i + 1 ) )
  **  (CharArray.undef_seg cur (i + 1 ) (i + 2 ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition all_prefixes_safety_wit_7 := 
forall (str_pre: Z) (str_l: (@list Z)) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (i: Z) (n: Z) (cur: Z) (out: Z) (data: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (n <= 100)) (PreH5 : (cur <> 0)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (valid_string str_l )) (PreH9 : (valid_prefixes_14 str_l )) (PreH10 : (problem_14_pre_z str_l )) (PreH11 : (prefix_rows_state_14 str_l i output_rows )) (PreH12 : ((Zlength (output_rows)) = i)) (PreH13 : ((Zlength (output_ptrs)) = i)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> n)
  **  (store_string str_pre str_l )
  **  (PtrArray.seg data 0 i output_ptrs )
  **  (PtrArray.undef_seg data i n )
  **  (prefix_rows_heap_14 output_ptrs output_rows )
  **  (CharArray.full cur (i + 1 ) (prefix_row_payload_14 (str_l) (i)) )
  **  (CharArray.undef_seg cur (i + 1 ) (i + 2 ) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition all_prefixes_safety_wit_8 := 
forall (str_pre: Z) (str_l: (@list Z)) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (i: Z) (n: Z) (cur: Z) (out: Z) (data: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (n <= 100)) (PreH5 : (cur <> 0)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (valid_string str_l )) (PreH9 : (valid_prefixes_14 str_l )) (PreH10 : (problem_14_pre_z str_l )) (PreH11 : (prefix_rows_state_14 str_l i output_rows )) (PreH12 : ((Zlength (output_rows)) = i)) (PreH13 : ((Zlength (output_ptrs)) = i)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> n)
  **  (store_string str_pre str_l )
  **  (PtrArray.seg data 0 i output_ptrs )
  **  (PtrArray.undef_seg data i n )
  **  (prefix_rows_heap_14 output_ptrs output_rows )
  **  (CharArray.full cur (i + 1 ) (prefix_row_payload_14 (str_l) (i)) )
  **  (CharArray.undef_seg cur (i + 1 ) (i + 2 ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition all_prefixes_safety_wit_9 := 
forall (str_pre: Z) (str_l: (@list Z)) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (i: Z) (n: Z) (cur: Z) (out: Z) (data: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (n <= 100)) (PreH5 : (cur <> 0)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (valid_string str_l )) (PreH9 : (valid_prefixes_14 str_l )) (PreH10 : (problem_14_pre_z str_l )) (PreH11 : (prefix_rows_state_14 str_l i output_rows )) (PreH12 : ((Zlength (output_rows)) = i)) (PreH13 : ((Zlength (output_ptrs)) = i)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> n)
  **  (store_string str_pre str_l )
  **  (PtrArray.seg data 0 i output_ptrs )
  **  (PtrArray.undef_seg data i n )
  **  (prefix_rows_heap_14 output_ptrs output_rows )
  **  (CharArray.full cur (i + 1 ) (prefix_row_payload_14 (str_l) (i)) )
  **  (CharArray.undef_seg cur (i + 1 ) (i + 2 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition all_prefixes_safety_wit_10 := 
forall (str_pre: Z) (str_l: (@list Z)) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (i: Z) (n: Z) (cur: Z) (out: Z) (data: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (n <= 100)) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (valid_string str_l )) (PreH8 : (valid_prefixes_14 str_l )) (PreH9 : (problem_14_pre_z str_l )) (PreH10 : (prefix_rows_state_14 str_l (i + 1 ) output_rows )) (PreH11 : ((Zlength (output_rows)) = (i + 1 ))) (PreH12 : ((Zlength (output_ptrs)) = (i + 1 ))) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> n)
  **  (store_string str_pre str_l )
  **  (PtrArray.seg data 0 (i + 1 ) output_ptrs )
  **  (PtrArray.undef_seg data (i + 1 ) n )
  **  (prefix_rows_heap_14 output_ptrs output_rows )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition all_prefixes_entail_wit_1 := 
(
forall (str_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (str_l)))) (PreH4 : (0 <= ((string_length (str_l)) + 1 ))) (PreH5 : (valid_string str_l )) (PreH6 : (valid_prefixes_14 str_l )) (PreH7 : ((string_length (str_l)) <= 100)) (PreH8 : (problem_14_pre_z str_l )) ,
  (PtrArray.undef_full retval_3 retval )
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_3)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> retval)
  **  (CharArray.full str_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
|--
  EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval = (string_length (str_l))) ” 
  &&  “ (retval <= 100) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval_3 <> 0) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (valid_prefixes_14 str_l ) ” 
  &&  “ (problem_14_pre_z str_l ) ” 
  &&  “ (prefix_rows_state_14 str_l 0 output_rows ) ” 
  &&  “ ((Zlength (output_rows)) = 0) ” 
  &&  “ ((Zlength (output_ptrs)) = 0) ”
  &&  ((&((retval_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_3)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> retval)
  **  (store_string str_pre str_l )
  **  (PtrArray.seg retval_3 0 0 output_ptrs )
  **  (PtrArray.undef_seg retval_3 0 retval )
  **  (prefix_rows_heap_14 output_ptrs output_rows )
) \/
(
forall (str_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (str_l)))) (PreH4 : (0 <= ((string_length (str_l)) + 1 ))) (PreH5 : (valid_string str_l )) (PreH6 : (valid_prefixes_14 str_l )) (PreH7 : ((string_length (str_l)) <= 100)) (PreH8 : (problem_14_pre_z str_l )) ,
  TT && emp 
|--
  EX (output_rows: (@list (@list Z))) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval = (string_length (str_l))) ” 
  &&  “ (retval <= 100) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval_3 <> 0) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (valid_prefixes_14 str_l ) ” 
  &&  “ (problem_14_pre_z str_l ) ” 
  &&  “ (prefix_rows_state_14 str_l 0 output_rows ) ” 
  &&  “ ((Zlength (output_rows)) = 0) ” 
  &&  “ ((Zlength ((@nil Z))) = 0) ”
  &&  (prefix_rows_heap_14 (@nil Z) output_rows )
).

Definition all_prefixes_entail_wit_2 := 
(
forall (str_pre: Z) (str_l: (@list Z)) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (data: Z) (out: Z) (n: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (i < n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (n <= 100)) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (valid_string str_l )) (PreH11 : (valid_prefixes_14 str_l )) (PreH12 : (problem_14_pre_z str_l )) (PreH13 : (prefix_rows_state_14 str_l i output_rows_2 )) (PreH14 : ((Zlength (output_rows_2)) = i)) (PreH15 : ((Zlength (output_ptrs_2)) = i)) ,
  (CharArray.undef_full retval (i + 2 ) )
  **  (CharArray.full str_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> n)
  **  (PtrArray.seg data 0 i output_ptrs_2 )
  **  (PtrArray.undef_seg data i n )
  **  (prefix_rows_heap_14 output_ptrs_2 output_rows_2 )
|--
  EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (n <= 100) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (valid_prefixes_14 str_l ) ” 
  &&  “ (problem_14_pre_z str_l ) ” 
  &&  “ (prefix_rows_state_14 str_l i output_rows ) ” 
  &&  “ ((Zlength (output_rows)) = i) ” 
  &&  “ ((Zlength (output_ptrs)) = i) ” 
  &&  “ ((Zlength ((prefix_row_payload_14 (str_l) (i)))) = (i + 1 )) ” 
  &&  “ (all_ascii (prefix_row_payload_14 (str_l) (i)) ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> n)
  **  (CharArray.full str_pre (i + 1 ) (prefix_row_payload_14 (str_l) (i)) )
  **  (CharArray.seg str_pre (i + 1 ) (n + 1 ) (sublist ((i + 1 )) ((n + 1 )) ((c_string (str_l)))) )
  **  (PtrArray.seg data 0 i output_ptrs )
  **  (PtrArray.undef_seg data i n )
  **  (prefix_rows_heap_14 output_ptrs output_rows )
  **  (CharArray.undef_full retval (i + 1 ) )
  **  (CharArray.undef_seg retval (i + 1 ) (i + 2 ) )
) \/
(
forall (str_pre: Z) (str_l: (@list Z)) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (data: Z) (out: Z) (n: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (i < n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (n <= 100)) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (valid_string str_l )) (PreH11 : (valid_prefixes_14 str_l )) (PreH12 : (problem_14_pre_z str_l )) (PreH13 : (prefix_rows_state_14 str_l i output_rows_2 )) (PreH14 : ((Zlength (output_rows_2)) = i)) (PreH15 : ((Zlength (output_ptrs_2)) = i)) ,
  (CharArray.undef_full retval (i + 2 ) )
  **  (CharArray.full str_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  (prefix_rows_heap_14 output_ptrs_2 output_rows_2 )
|--
  EX (output_rows: (@list (@list Z))) ,
  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (n <= 100) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (valid_prefixes_14 str_l ) ” 
  &&  “ (problem_14_pre_z str_l ) ” 
  &&  “ (prefix_rows_state_14 str_l i output_rows ) ” 
  &&  “ ((Zlength (output_rows)) = i) ” 
  &&  “ ((Zlength (output_ptrs_2)) = i) ” 
  &&  “ ((Zlength ((prefix_row_payload_14 (str_l) (i)))) = (i + 1 )) ” 
  &&  “ (all_ascii (prefix_row_payload_14 (str_l) (i)) ) ”
  &&  (CharArray.full str_pre (i + 1 ) (prefix_row_payload_14 (str_l) (i)) )
  **  (CharArray.seg str_pre (i + 1 ) (n + 1 ) (sublist ((i + 1 )) ((n + 1 )) ((c_string (str_l)))) )
  **  (prefix_rows_heap_14 output_ptrs_2 output_rows )
  **  (CharArray.undef_full retval (i + 1 ) )
  **  (CharArray.undef_seg retval (i + 1 ) (i + 2 ) )
).

Definition all_prefixes_entail_wit_3 := 
(
forall (str_pre: Z) (str_l: (@list Z)) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (i: Z) (n: Z) (cur: Z) (out: Z) (data: Z) (retval: Z) (PreH1 : (retval = cur)) (PreH2 : (0 <= i)) (PreH3 : (i < n)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (n <= 100)) (PreH6 : (cur <> 0)) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (valid_string str_l )) (PreH10 : (valid_prefixes_14 str_l )) (PreH11 : (problem_14_pre_z str_l )) (PreH12 : (prefix_rows_state_14 str_l i output_rows_2 )) (PreH13 : ((Zlength (output_rows_2)) = i)) (PreH14 : ((Zlength (output_ptrs_2)) = i)) (PreH15 : ((Zlength ((prefix_row_payload_14 (str_l) (i)))) = (i + 1 ))) (PreH16 : (all_ascii (prefix_row_payload_14 (str_l) (i)) )) ,
  (CharArray.full cur (i + 1 ) (prefix_row_payload_14 (str_l) (i)) )
  **  (CharArray.full str_pre (i + 1 ) (prefix_row_payload_14 (str_l) (i)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> n)
  **  (CharArray.seg str_pre (i + 1 ) (n + 1 ) (sublist ((i + 1 )) ((n + 1 )) ((c_string (str_l)))) )
  **  (PtrArray.seg data 0 i output_ptrs_2 )
  **  (PtrArray.undef_seg data i n )
  **  (prefix_rows_heap_14 output_ptrs_2 output_rows_2 )
  **  (CharArray.undef_seg cur (i + 1 ) (i + 2 ) )
|--
  EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (n <= 100) ” 
  &&  “ (cur <> 0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (valid_prefixes_14 str_l ) ” 
  &&  “ (problem_14_pre_z str_l ) ” 
  &&  “ (prefix_rows_state_14 str_l i output_rows ) ” 
  &&  “ ((Zlength (output_rows)) = i) ” 
  &&  “ ((Zlength (output_ptrs)) = i) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> n)
  **  (store_string str_pre str_l )
  **  (PtrArray.seg data 0 i output_ptrs )
  **  (PtrArray.undef_seg data i n )
  **  (prefix_rows_heap_14 output_ptrs output_rows )
  **  (CharArray.full cur (i + 1 ) (prefix_row_payload_14 (str_l) (i)) )
  **  (CharArray.undef_seg cur (i + 1 ) (i + 2 ) )
) \/
(
forall (str_pre: Z) (str_l: (@list Z)) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (i: Z) (n: Z) (cur: Z) (out: Z) (data: Z) (retval: Z) (PreH1 : (0 <= (i + 1 ))) (PreH2 : (retval = cur)) (PreH3 : (0 <= i)) (PreH4 : (i < n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (n <= 100)) (PreH7 : (cur <> 0)) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (valid_string str_l )) (PreH11 : (valid_prefixes_14 str_l )) (PreH12 : (problem_14_pre_z str_l )) (PreH13 : (prefix_rows_state_14 str_l i output_rows_2 )) (PreH14 : ((Zlength (output_rows_2)) = i)) (PreH15 : ((Zlength (output_ptrs_2)) = i)) (PreH16 : ((Zlength ((prefix_row_payload_14 (str_l) (i)))) = (i + 1 ))) (PreH17 : (all_ascii (prefix_row_payload_14 (str_l) (i)) )) ,
  (CharArray.full str_pre (i + 1 ) (prefix_row_payload_14 (str_l) (i)) )
  **  (CharArray.seg str_pre (i + 1 ) (n + 1 ) (sublist ((i + 1 )) ((n + 1 )) ((c_string (str_l)))) )
  **  (prefix_rows_heap_14 output_ptrs_2 output_rows_2 )
|--
  EX (output_rows: (@list (@list Z))) ,
  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (n <= 100) ” 
  &&  “ (cur <> 0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (valid_prefixes_14 str_l ) ” 
  &&  “ (problem_14_pre_z str_l ) ” 
  &&  “ (prefix_rows_state_14 str_l i output_rows ) ” 
  &&  “ ((Zlength (output_rows)) = i) ” 
  &&  “ ((Zlength (output_ptrs_2)) = i) ”
  &&  (CharArray.full str_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  (prefix_rows_heap_14 output_ptrs_2 output_rows )
).

Definition all_prefixes_entail_wit_4 := 
(
forall (str_pre: Z) (str_l: (@list Z)) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (i: Z) (n: Z) (cur: Z) (out: Z) (data: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (0 <= (i + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (n <= 100)) (PreH7 : (cur <> 0)) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (valid_string str_l )) (PreH11 : (valid_prefixes_14 str_l )) (PreH12 : (problem_14_pre_z str_l )) (PreH13 : (prefix_rows_state_14 str_l i output_rows_2 )) (PreH14 : ((Zlength (output_rows_2)) = i)) (PreH15 : ((Zlength (output_ptrs_2)) = i)) ,
  (CharArray.full cur ((i + 1 ) + 1 ) (app ((prefix_row_payload_14 (str_l) (i))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg cur ((i + 1 ) + 1 ) (i + 2 ) )
  **  (CharArray.full str_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> n)
  **  (PtrArray.seg data 0 i output_ptrs_2 )
  **  (PtrArray.undef_seg data i n )
  **  (prefix_rows_heap_14 output_ptrs_2 output_rows_2 )
|--
  EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (n <= 100) ” 
  &&  “ (cur <> 0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (valid_prefixes_14 str_l ) ” 
  &&  “ (problem_14_pre_z str_l ) ” 
  &&  “ (prefix_rows_state_14 str_l i output_rows ) ” 
  &&  “ ((Zlength (output_rows)) = i) ” 
  &&  “ ((Zlength (output_ptrs)) = i) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> n)
  **  (store_string str_pre str_l )
  **  (PtrArray.seg data 0 i output_ptrs )
  **  (PtrArray.undef_seg data i n )
  **  (prefix_rows_heap_14 output_ptrs output_rows )
  **  (CharArray.full cur (i + 2 ) (prefix_row_14 (str_l) (i)) )
) \/
(
forall (str_l: (@list Z)) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (i: Z) (n: Z) (cur: Z) (out: Z) (data: Z) (PreH1 : (0 <= ((i + 1 ) + 1 ))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (0 <= (i + 1 ))) (PreH4 : (0 <= i)) (PreH5 : (i < n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (n <= 100)) (PreH8 : (cur <> 0)) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (valid_string str_l )) (PreH12 : (valid_prefixes_14 str_l )) (PreH13 : (problem_14_pre_z str_l )) (PreH14 : (prefix_rows_state_14 str_l i output_rows_2 )) (PreH15 : ((Zlength (output_rows_2)) = i)) (PreH16 : ((Zlength (output_ptrs_2)) = i)) ,
  (CharArray.full cur ((i + 1 ) + 1 ) (app ((prefix_row_payload_14 (str_l) (i))) ((cons (0) ((@nil Z))))) )
  **  (prefix_rows_heap_14 output_ptrs_2 output_rows_2 )
|--
  EX (output_rows: (@list (@list Z))) ,
  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (n <= 100) ” 
  &&  “ (cur <> 0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (valid_prefixes_14 str_l ) ” 
  &&  “ (problem_14_pre_z str_l ) ” 
  &&  “ (prefix_rows_state_14 str_l i output_rows ) ” 
  &&  “ ((Zlength (output_rows)) = i) ” 
  &&  “ ((Zlength (output_ptrs_2)) = i) ”
  &&  (prefix_rows_heap_14 output_ptrs_2 output_rows )
  **  (CharArray.full cur (i + 2 ) (prefix_row_14 (str_l) (i)) )
).

Definition all_prefixes_entail_wit_5 := 
(
forall (str_pre: Z) (str_l: (@list Z)) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (i: Z) (n: Z) (cur: Z) (out: Z) (data: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (0 <= (i + 2 ))) (PreH3 : (0 <= i)) (PreH4 : (i < n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (n <= 100)) (PreH7 : (cur <> 0)) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (valid_string str_l )) (PreH11 : (valid_prefixes_14 str_l )) (PreH12 : (problem_14_pre_z str_l )) (PreH13 : (prefix_rows_state_14 str_l i output_rows_2 )) (PreH14 : ((Zlength (output_rows_2)) = i)) (PreH15 : ((Zlength (output_ptrs_2)) = i)) ,
  (PtrArray.seg data 0 (i + 1 ) (app (output_ptrs_2) ((cons (cur) ((@nil Z))))) )
  **  (PtrArray.undef_seg data (i + 1 ) n )
  **  (CharArray.full str_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> n)
  **  (prefix_rows_heap_14 output_ptrs_2 output_rows_2 )
  **  (CharArray.full cur (i + 2 ) (prefix_row_14 (str_l) (i)) )
|--
  EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (n <= 100) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (valid_prefixes_14 str_l ) ” 
  &&  “ (problem_14_pre_z str_l ) ” 
  &&  “ (prefix_rows_state_14 str_l (i + 1 ) output_rows ) ” 
  &&  “ ((Zlength (output_rows)) = (i + 1 )) ” 
  &&  “ ((Zlength (output_ptrs)) = (i + 1 )) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> n)
  **  (store_string str_pre str_l )
  **  (PtrArray.seg data 0 (i + 1 ) output_ptrs )
  **  (PtrArray.undef_seg data (i + 1 ) n )
  **  (prefix_rows_heap_14 output_ptrs output_rows )
) \/
(
forall (str_l: (@list Z)) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (i: Z) (n: Z) (cur: Z) (out: Z) (data: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (0 <= (i + 2 ))) (PreH3 : (0 <= i)) (PreH4 : (i < n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (n <= 100)) (PreH7 : (cur <> 0)) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (valid_string str_l )) (PreH11 : (valid_prefixes_14 str_l )) (PreH12 : (problem_14_pre_z str_l )) (PreH13 : (prefix_rows_state_14 str_l i output_rows_2 )) (PreH14 : ((Zlength (output_rows_2)) = i)) (PreH15 : ((Zlength (output_ptrs_2)) = i)) ,
  (prefix_rows_heap_14 output_ptrs_2 output_rows_2 )
  **  (CharArray.full cur (i + 2 ) (prefix_row_14 (str_l) (i)) )
|--
  EX (output_rows: (@list (@list Z))) ,
  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (n <= 100) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (valid_prefixes_14 str_l ) ” 
  &&  “ (problem_14_pre_z str_l ) ” 
  &&  “ (prefix_rows_state_14 str_l (i + 1 ) output_rows ) ” 
  &&  “ ((Zlength (output_rows)) = (i + 1 )) ” 
  &&  “ ((Zlength ((app (output_ptrs_2) ((cons (cur) ((@nil Z))))))) = (i + 1 )) ”
  &&  (prefix_rows_heap_14 (app (output_ptrs_2) ((cons (cur) ((@nil Z))))) output_rows )
).

Definition all_prefixes_entail_wit_6 := 
forall (str_pre: Z) (str_l: (@list Z)) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (i: Z) (n: Z) (out: Z) (data: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (n <= 100)) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (valid_string str_l )) (PreH8 : (valid_prefixes_14 str_l )) (PreH9 : (problem_14_pre_z str_l )) (PreH10 : (prefix_rows_state_14 str_l (i + 1 ) output_rows_2 )) (PreH11 : ((Zlength (output_rows_2)) = (i + 1 ))) (PreH12 : ((Zlength (output_ptrs_2)) = (i + 1 ))) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> n)
  **  (store_string str_pre str_l )
  **  (PtrArray.seg data 0 (i + 1 ) output_ptrs_2 )
  **  (PtrArray.undef_seg data (i + 1 ) n )
  **  (prefix_rows_heap_14 output_ptrs_2 output_rows_2 )
|--
  EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (n <= 100) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (valid_prefixes_14 str_l ) ” 
  &&  “ (problem_14_pre_z str_l ) ” 
  &&  “ (prefix_rows_state_14 str_l (i + 1 ) output_rows ) ” 
  &&  “ ((Zlength (output_rows)) = (i + 1 )) ” 
  &&  “ ((Zlength (output_ptrs)) = (i + 1 )) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> n)
  **  (store_string str_pre str_l )
  **  (PtrArray.seg data 0 (i + 1 ) output_ptrs )
  **  (PtrArray.undef_seg data (i + 1 ) n )
  **  (prefix_rows_heap_14 output_ptrs output_rows )
.

Definition all_prefixes_entail_wit_7 := 
(
forall (str_pre: Z) (str_l: (@list Z)) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (i >= n)) (PreH2 : (0 <= i)) (PreH3 : (i <= n)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (n <= 100)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (valid_string str_l )) (PreH9 : (valid_prefixes_14 str_l )) (PreH10 : (problem_14_pre_z str_l )) (PreH11 : (prefix_rows_state_14 str_l i output_rows_2 )) (PreH12 : ((Zlength (output_rows_2)) = i)) (PreH13 : ((Zlength (output_ptrs_2)) = i)) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> n)
  **  (store_string str_pre str_l )
  **  (PtrArray.seg data 0 i output_ptrs_2 )
  **  (PtrArray.undef_seg data i n )
  **  (prefix_rows_heap_14 output_ptrs_2 output_rows_2 )
|--
  EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
  “ (n = (string_length (str_l))) ” 
  &&  “ (n <= 100) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (valid_prefixes_14 str_l ) ” 
  &&  “ (problem_14_pre_z str_l ) ” 
  &&  “ (prefix_rows_state_14 str_l n output_rows ) ” 
  &&  “ ((Zlength (output_rows)) = n) ” 
  &&  “ ((Zlength (output_ptrs)) = n) ” 
  &&  “ (problem_14_spec_z str_l output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> n)
  **  (store_string str_pre str_l )
  **  (PtrArray.seg data 0 n output_ptrs )
  **  (prefix_rows_heap_14 output_ptrs output_rows )
) \/
(
forall (str_l: (@list Z)) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (i >= n)) (PreH3 : (0 <= i)) (PreH4 : (i <= n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (n <= 100)) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (valid_string str_l )) (PreH10 : (valid_prefixes_14 str_l )) (PreH11 : (problem_14_pre_z str_l )) (PreH12 : (prefix_rows_state_14 str_l i output_rows_2 )) (PreH13 : ((Zlength (output_rows_2)) = i)) (PreH14 : ((Zlength (output_ptrs_2)) = i)) ,
  (PtrArray.seg data 0 i output_ptrs_2 )
  **  (prefix_rows_heap_14 output_ptrs_2 output_rows_2 )
|--
  EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
  “ (n = (string_length (str_l))) ” 
  &&  “ (n <= 100) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (valid_prefixes_14 str_l ) ” 
  &&  “ (problem_14_pre_z str_l ) ” 
  &&  “ (prefix_rows_state_14 str_l n output_rows ) ” 
  &&  “ ((Zlength (output_rows)) = n) ” 
  &&  “ ((Zlength (output_ptrs)) = n) ” 
  &&  “ (problem_14_spec_z str_l output_rows ) ”
  &&  (PtrArray.seg data 0 n output_ptrs )
  **  (prefix_rows_heap_14 output_ptrs output_rows )
).

Definition all_prefixes_return_wit_1 := 
(
forall (str_pre: Z) (str_l: (@list Z)) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (n: Z) (out: Z) (data_2: Z) (PreH1 : (n = (string_length (str_l)))) (PreH2 : (n <= 100)) (PreH3 : (out <> 0)) (PreH4 : (data_2 <> 0)) (PreH5 : (valid_string str_l )) (PreH6 : (valid_prefixes_14 str_l )) (PreH7 : (problem_14_pre_z str_l )) (PreH8 : (prefix_rows_state_14 str_l n output_rows_2 )) (PreH9 : ((Zlength (output_rows_2)) = n)) (PreH10 : ((Zlength (output_ptrs_2)) = n)) (PreH11 : (problem_14_spec_z str_l output_rows_2 )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data_2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> n)
  **  (store_string str_pre str_l )
  **  (PtrArray.seg data_2 0 n output_ptrs_2 )
  **  (prefix_rows_heap_14 output_ptrs_2 output_rows_2 )
|--
  EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z)))  (data: Z) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ ((Zlength (output_rows)) = (string_length (str_l))) ” 
  &&  “ ((Zlength (output_ptrs)) = (string_length (str_l))) ” 
  &&  “ (problem_14_spec_z str_l output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (string_length (str_l)))
  **  (store_string str_pre str_l )
  **  (PtrArray.seg data 0 (string_length (str_l)) output_ptrs )
  **  (prefix_rows_heap_14 output_ptrs output_rows )
) \/
(
forall (str_l: (@list Z)) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (n: Z) (out: Z) (data_2: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (n = (string_length (str_l)))) (PreH3 : (n <= 100)) (PreH4 : (out <> 0)) (PreH5 : (data_2 <> 0)) (PreH6 : (valid_string str_l )) (PreH7 : (valid_prefixes_14 str_l )) (PreH8 : (problem_14_pre_z str_l )) (PreH9 : (prefix_rows_state_14 str_l n output_rows_2 )) (PreH10 : ((Zlength (output_rows_2)) = n)) (PreH11 : ((Zlength (output_ptrs_2)) = n)) (PreH12 : (problem_14_spec_z str_l output_rows_2 )) ,
  (PtrArray.seg data_2 0 n output_ptrs_2 )
  **  (prefix_rows_heap_14 output_ptrs_2 output_rows_2 )
|--
  EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data_2 <> 0) ” 
  &&  “ ((Zlength (output_rows)) = (string_length (str_l))) ” 
  &&  “ ((Zlength (output_ptrs)) = (string_length (str_l))) ” 
  &&  “ (problem_14_spec_z str_l output_rows ) ”
  &&  (PtrArray.seg data_2 0 (string_length (str_l)) output_ptrs )
  **  (prefix_rows_heap_14 output_ptrs output_rows )
).

Definition all_prefixes_partial_solve_wit_1_pure := 
forall (str_pre: Z) (str_l: (@list Z)) (PreH1 : (valid_string str_l )) (PreH2 : (valid_prefixes_14 str_l )) (PreH3 : ((string_length (str_l)) <= 100)) (PreH4 : (problem_14_pre_z str_l )) ,
  ((( &( "n" ) )) # Int  |->_)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  (store_string str_pre str_l )
|--
  “ (valid_string str_l ) ” 
  &&  “ ((string_length (str_l)) < INT_MAX) ”
.

Definition all_prefixes_partial_solve_wit_1_aux := 
forall (str_pre: Z) (str_l: (@list Z)) (PreH1 : (valid_string str_l )) (PreH2 : (valid_prefixes_14 str_l )) (PreH3 : ((string_length (str_l)) <= 100)) (PreH4 : (problem_14_pre_z str_l )) ,
  (store_string str_pre str_l )
|--
  “ (valid_string str_l ) ” 
  &&  “ ((string_length (str_l)) < INT_MAX) ” 
  &&  “ (0 <= ((string_length (str_l)) + 1 )) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (valid_prefixes_14 str_l ) ” 
  &&  “ ((string_length (str_l)) <= 100) ” 
  &&  “ (problem_14_pre_z str_l ) ”
  &&  (store_string str_pre str_l )
.

Definition all_prefixes_partial_solve_wit_1 := all_prefixes_partial_solve_wit_1_pure -> all_prefixes_partial_solve_wit_1_aux.

Definition all_prefixes_partial_solve_wit_2 := 
forall (str_pre: Z) (str_l: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (str_l)))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (valid_string str_l )) (PreH4 : (valid_prefixes_14 str_l )) (PreH5 : ((string_length (str_l)) <= 100)) (PreH6 : (problem_14_pre_z str_l )) ,
  (store_string str_pre str_l )
|--
  “ (retval = (string_length (str_l))) ” 
  &&  “ (0 <= ((string_length (str_l)) + 1 )) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (valid_prefixes_14 str_l ) ” 
  &&  “ ((string_length (str_l)) <= 100) ” 
  &&  “ (problem_14_pre_z str_l ) ”
  &&  (CharArray.full str_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
.

Definition all_prefixes_partial_solve_wit_3_pure := 
(
forall (str_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval = (string_length (str_l)))) (PreH3 : (0 <= ((string_length (str_l)) + 1 ))) (PreH4 : (valid_string str_l )) (PreH5 : (valid_prefixes_14 str_l )) (PreH6 : ((string_length (str_l)) <= 100)) (PreH7 : (problem_14_pre_z str_l )) ,
  ((&((retval_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> retval)
  **  (CharArray.full str_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
|--
  “ (retval < INT_MAX) ” 
  &&  “ (0 <= retval) ”
) \/
(
forall (str_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval <= INT_MAX)) (PreH2 : (retval >= INT_MIN)) (PreH3 : (retval_2 <> 0)) (PreH4 : (retval = (string_length (str_l)))) (PreH5 : (0 <= ((string_length (str_l)) + 1 ))) (PreH6 : (valid_string str_l )) (PreH7 : (valid_prefixes_14 str_l )) (PreH8 : ((string_length (str_l)) <= 100)) (PreH9 : (problem_14_pre_z str_l )) ,
  ((&((retval_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> retval)
  **  (CharArray.full str_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
|--
  “ (0 <= retval) ”
).

Definition all_prefixes_partial_solve_wit_3_pure_split_goal_1 := 
forall (str_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval <= INT_MAX)) (PreH2 : (retval >= INT_MIN)) (PreH3 : (retval_2 <> 0)) (PreH4 : (retval = (string_length (str_l)))) (PreH5 : (0 <= ((string_length (str_l)) + 1 ))) (PreH6 : (valid_string str_l )) (PreH7 : (valid_prefixes_14 str_l )) (PreH8 : ((string_length (str_l)) <= 100)) (PreH9 : (problem_14_pre_z str_l )) ,
  ((&((retval_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> retval)
  **  (CharArray.full str_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
|--
  “ (0 <= retval) ”
.

Definition all_prefixes_partial_solve_wit_3_aux := 
forall (str_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval = (string_length (str_l)))) (PreH3 : (0 <= ((string_length (str_l)) + 1 ))) (PreH4 : (valid_string str_l )) (PreH5 : (valid_prefixes_14 str_l )) (PreH6 : ((string_length (str_l)) <= 100)) (PreH7 : (problem_14_pre_z str_l )) ,
  ((&((retval_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> retval)
  **  (CharArray.full str_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
|--
  “ (retval < INT_MAX) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval = (string_length (str_l))) ” 
  &&  “ (0 <= ((string_length (str_l)) + 1 )) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (valid_prefixes_14 str_l ) ” 
  &&  “ ((string_length (str_l)) <= 100) ” 
  &&  “ (problem_14_pre_z str_l ) ”
  &&  ((&((retval_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> retval)
  **  (CharArray.full str_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
.

Definition all_prefixes_partial_solve_wit_3 := all_prefixes_partial_solve_wit_3_pure -> all_prefixes_partial_solve_wit_3_aux.

Definition all_prefixes_partial_solve_wit_4_pure := 
forall (str_pre: Z) (str_l: (@list Z)) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (cur: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (i < n)) (PreH2 : (0 <= i)) (PreH3 : (i <= n)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (n <= 100)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (valid_string str_l )) (PreH9 : (valid_prefixes_14 str_l )) (PreH10 : (problem_14_pre_z str_l )) (PreH11 : (prefix_rows_state_14 str_l i output_rows )) (PreH12 : ((Zlength (output_rows)) = i)) (PreH13 : ((Zlength (output_ptrs)) = i)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> n)
  **  (store_string str_pre str_l )
  **  (PtrArray.seg data 0 i output_ptrs )
  **  (PtrArray.undef_seg data i n )
  **  (prefix_rows_heap_14 output_ptrs output_rows )
|--
  “ ((i + 2 ) > 0) ” 
  &&  “ ((i + 2 ) < INT_MAX) ”
.

Definition all_prefixes_partial_solve_wit_4_aux := 
forall (str_pre: Z) (str_l: (@list Z)) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (i < n)) (PreH2 : (0 <= i)) (PreH3 : (i <= n)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (n <= 100)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (valid_string str_l )) (PreH9 : (valid_prefixes_14 str_l )) (PreH10 : (problem_14_pre_z str_l )) (PreH11 : (prefix_rows_state_14 str_l i output_rows )) (PreH12 : ((Zlength (output_rows)) = i)) (PreH13 : ((Zlength (output_ptrs)) = i)) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> n)
  **  (store_string str_pre str_l )
  **  (PtrArray.seg data 0 i output_ptrs )
  **  (PtrArray.undef_seg data i n )
  **  (prefix_rows_heap_14 output_ptrs output_rows )
|--
  “ ((i + 2 ) > 0) ” 
  &&  “ ((i + 2 ) < INT_MAX) ” 
  &&  “ (0 <= ((string_length (str_l)) + 1 )) ” 
  &&  “ (i < n) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (n <= 100) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (valid_prefixes_14 str_l ) ” 
  &&  “ (problem_14_pre_z str_l ) ” 
  &&  “ (prefix_rows_state_14 str_l i output_rows ) ” 
  &&  “ ((Zlength (output_rows)) = i) ” 
  &&  “ ((Zlength (output_ptrs)) = i) ”
  &&  (CharArray.full str_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> n)
  **  (PtrArray.seg data 0 i output_ptrs )
  **  (PtrArray.undef_seg data i n )
  **  (prefix_rows_heap_14 output_ptrs output_rows )
.

Definition all_prefixes_partial_solve_wit_4 := all_prefixes_partial_solve_wit_4_pure -> all_prefixes_partial_solve_wit_4_aux.

Definition all_prefixes_partial_solve_wit_5_pure := 
forall (str_pre: Z) (str_l: (@list Z)) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (i: Z) (n: Z) (cur: Z) (out: Z) (data: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (n <= 100)) (PreH5 : (cur <> 0)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (valid_string str_l )) (PreH9 : (valid_prefixes_14 str_l )) (PreH10 : (problem_14_pre_z str_l )) (PreH11 : (prefix_rows_state_14 str_l i output_rows )) (PreH12 : ((Zlength (output_rows)) = i)) (PreH13 : ((Zlength (output_ptrs)) = i)) (PreH14 : ((Zlength ((prefix_row_payload_14 (str_l) (i)))) = (i + 1 ))) (PreH15 : (all_ascii (prefix_row_payload_14 (str_l) (i)) )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> n)
  **  (CharArray.full str_pre (i + 1 ) (prefix_row_payload_14 (str_l) (i)) )
  **  (CharArray.seg str_pre (i + 1 ) (n + 1 ) (sublist ((i + 1 )) ((n + 1 )) ((c_string (str_l)))) )
  **  (PtrArray.seg data 0 i output_ptrs )
  **  (PtrArray.undef_seg data i n )
  **  (prefix_rows_heap_14 output_ptrs output_rows )
  **  (CharArray.undef_full cur (i + 1 ) )
  **  (CharArray.undef_seg cur (i + 1 ) (i + 2 ) )
|--
  “ (all_ascii (prefix_row_payload_14 (str_l) (i)) ) ” 
  &&  “ ((Zlength ((prefix_row_payload_14 (str_l) (i)))) = (i + 1 )) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) < INT_MAX) ”
.

Definition all_prefixes_partial_solve_wit_5_aux := 
forall (str_pre: Z) (str_l: (@list Z)) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (i: Z) (n: Z) (cur: Z) (out: Z) (data: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (n <= 100)) (PreH5 : (cur <> 0)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (valid_string str_l )) (PreH9 : (valid_prefixes_14 str_l )) (PreH10 : (problem_14_pre_z str_l )) (PreH11 : (prefix_rows_state_14 str_l i output_rows )) (PreH12 : ((Zlength (output_rows)) = i)) (PreH13 : ((Zlength (output_ptrs)) = i)) (PreH14 : ((Zlength ((prefix_row_payload_14 (str_l) (i)))) = (i + 1 ))) (PreH15 : (all_ascii (prefix_row_payload_14 (str_l) (i)) )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> n)
  **  (CharArray.full str_pre (i + 1 ) (prefix_row_payload_14 (str_l) (i)) )
  **  (CharArray.seg str_pre (i + 1 ) (n + 1 ) (sublist ((i + 1 )) ((n + 1 )) ((c_string (str_l)))) )
  **  (PtrArray.seg data 0 i output_ptrs )
  **  (PtrArray.undef_seg data i n )
  **  (prefix_rows_heap_14 output_ptrs output_rows )
  **  (CharArray.undef_full cur (i + 1 ) )
  **  (CharArray.undef_seg cur (i + 1 ) (i + 2 ) )
|--
  “ (all_ascii (prefix_row_payload_14 (str_l) (i)) ) ” 
  &&  “ ((Zlength ((prefix_row_payload_14 (str_l) (i)))) = (i + 1 )) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (n <= 100) ” 
  &&  “ (cur <> 0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (valid_prefixes_14 str_l ) ” 
  &&  “ (problem_14_pre_z str_l ) ” 
  &&  “ (prefix_rows_state_14 str_l i output_rows ) ” 
  &&  “ ((Zlength (output_rows)) = i) ” 
  &&  “ ((Zlength (output_ptrs)) = i) ” 
  &&  “ ((Zlength ((prefix_row_payload_14 (str_l) (i)))) = (i + 1 )) ” 
  &&  “ (all_ascii (prefix_row_payload_14 (str_l) (i)) ) ”
  &&  (CharArray.undef_full cur (i + 1 ) )
  **  (CharArray.full str_pre (i + 1 ) (prefix_row_payload_14 (str_l) (i)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> n)
  **  (CharArray.seg str_pre (i + 1 ) (n + 1 ) (sublist ((i + 1 )) ((n + 1 )) ((c_string (str_l)))) )
  **  (PtrArray.seg data 0 i output_ptrs )
  **  (PtrArray.undef_seg data i n )
  **  (prefix_rows_heap_14 output_ptrs output_rows )
  **  (CharArray.undef_seg cur (i + 1 ) (i + 2 ) )
.

Definition all_prefixes_partial_solve_wit_5 := all_prefixes_partial_solve_wit_5_pure -> all_prefixes_partial_solve_wit_5_aux.

Definition all_prefixes_partial_solve_wit_6 := 
forall (str_pre: Z) (str_l: (@list Z)) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (i: Z) (n: Z) (cur: Z) (out: Z) (data: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (n <= 100)) (PreH5 : (cur <> 0)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (valid_string str_l )) (PreH9 : (valid_prefixes_14 str_l )) (PreH10 : (problem_14_pre_z str_l )) (PreH11 : (prefix_rows_state_14 str_l i output_rows )) (PreH12 : ((Zlength (output_rows)) = i)) (PreH13 : ((Zlength (output_ptrs)) = i)) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> n)
  **  (store_string str_pre str_l )
  **  (PtrArray.seg data 0 i output_ptrs )
  **  (PtrArray.undef_seg data i n )
  **  (prefix_rows_heap_14 output_ptrs output_rows )
  **  (CharArray.full cur (i + 1 ) (prefix_row_payload_14 (str_l) (i)) )
  **  (CharArray.undef_seg cur (i + 1 ) (i + 2 ) )
|--
  “ (0 <= ((string_length (str_l)) + 1 )) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (n <= 100) ” 
  &&  “ (cur <> 0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (valid_prefixes_14 str_l ) ” 
  &&  “ (problem_14_pre_z str_l ) ” 
  &&  “ (prefix_rows_state_14 str_l i output_rows ) ” 
  &&  “ ((Zlength (output_rows)) = i) ” 
  &&  “ ((Zlength (output_ptrs)) = i) ”
  &&  (((cur + ((i + 1 ) * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.full str_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  (CharArray.undef_missing_i cur (i + 1 ) (i + 1 ) (i + 2 ) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> n)
  **  (PtrArray.seg data 0 i output_ptrs )
  **  (PtrArray.undef_seg data i n )
  **  (prefix_rows_heap_14 output_ptrs output_rows )
  **  (CharArray.full cur (i + 1 ) (prefix_row_payload_14 (str_l) (i)) )
.

Definition all_prefixes_partial_solve_wit_7 := 
forall (str_pre: Z) (str_l: (@list Z)) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (i: Z) (n: Z) (cur: Z) (out: Z) (data: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (n <= 100)) (PreH5 : (cur <> 0)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (valid_string str_l )) (PreH9 : (valid_prefixes_14 str_l )) (PreH10 : (problem_14_pre_z str_l )) (PreH11 : (prefix_rows_state_14 str_l i output_rows )) (PreH12 : ((Zlength (output_rows)) = i)) (PreH13 : ((Zlength (output_ptrs)) = i)) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> n)
  **  (store_string str_pre str_l )
  **  (PtrArray.seg data 0 i output_ptrs )
  **  (PtrArray.undef_seg data i n )
  **  (prefix_rows_heap_14 output_ptrs output_rows )
  **  (CharArray.full cur (i + 2 ) (prefix_row_14 (str_l) (i)) )
|--
  “ (0 <= ((string_length (str_l)) + 1 )) ” 
  &&  “ (0 <= (i + 2 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (n <= 100) ” 
  &&  “ (cur <> 0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (valid_prefixes_14 str_l ) ” 
  &&  “ (problem_14_pre_z str_l ) ” 
  &&  “ (prefix_rows_state_14 str_l i output_rows ) ” 
  &&  “ ((Zlength (output_rows)) = i) ” 
  &&  “ ((Zlength (output_ptrs)) = i) ”
  &&  (((data + (i * sizeof(PTR) ) )) # Ptr  |->_)
  **  (PtrArray.undef_seg data (i + 1 ) n )
  **  (CharArray.full str_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> n)
  **  (PtrArray.seg data 0 i output_ptrs )
  **  (prefix_rows_heap_14 output_ptrs output_rows )
  **  (CharArray.full cur (i + 2 ) (prefix_row_14 (str_l) (i)) )
.

Module Type VC_Correct.

Include ptr_array2_Strategy_Correct.
Include char_array_Strategy_Correct.
Include string_Strategy_Correct.

Axiom proof_of_all_prefixes_safety_wit_1 : all_prefixes_safety_wit_1.
Axiom proof_of_all_prefixes_safety_wit_2 : all_prefixes_safety_wit_2.
Axiom proof_of_all_prefixes_safety_wit_3 : all_prefixes_safety_wit_3.
Axiom proof_of_all_prefixes_safety_wit_4 : all_prefixes_safety_wit_4.
Axiom proof_of_all_prefixes_safety_wit_5 : all_prefixes_safety_wit_5.
Axiom proof_of_all_prefixes_safety_wit_6 : all_prefixes_safety_wit_6.
Axiom proof_of_all_prefixes_safety_wit_7 : all_prefixes_safety_wit_7.
Axiom proof_of_all_prefixes_safety_wit_8 : all_prefixes_safety_wit_8.
Axiom proof_of_all_prefixes_safety_wit_9 : all_prefixes_safety_wit_9.
Axiom proof_of_all_prefixes_safety_wit_10 : all_prefixes_safety_wit_10.
Axiom proof_of_all_prefixes_entail_wit_1 : all_prefixes_entail_wit_1.
Axiom proof_of_all_prefixes_entail_wit_2 : all_prefixes_entail_wit_2.
Axiom proof_of_all_prefixes_entail_wit_3 : all_prefixes_entail_wit_3.
Axiom proof_of_all_prefixes_entail_wit_4 : all_prefixes_entail_wit_4.
Axiom proof_of_all_prefixes_entail_wit_5 : all_prefixes_entail_wit_5.
Axiom proof_of_all_prefixes_entail_wit_6 : all_prefixes_entail_wit_6.
Axiom proof_of_all_prefixes_entail_wit_7 : all_prefixes_entail_wit_7.
Axiom proof_of_all_prefixes_return_wit_1 : all_prefixes_return_wit_1.
Axiom proof_of_all_prefixes_partial_solve_wit_1_pure : all_prefixes_partial_solve_wit_1_pure.
Axiom proof_of_all_prefixes_partial_solve_wit_1 : all_prefixes_partial_solve_wit_1.
Axiom proof_of_all_prefixes_partial_solve_wit_2 : all_prefixes_partial_solve_wit_2.
Axiom proof_of_all_prefixes_partial_solve_wit_3_pure : all_prefixes_partial_solve_wit_3_pure.
Axiom proof_of_all_prefixes_partial_solve_wit_3 : all_prefixes_partial_solve_wit_3.
Axiom proof_of_all_prefixes_partial_solve_wit_4_pure : all_prefixes_partial_solve_wit_4_pure.
Axiom proof_of_all_prefixes_partial_solve_wit_4 : all_prefixes_partial_solve_wit_4.
Axiom proof_of_all_prefixes_partial_solve_wit_5_pure : all_prefixes_partial_solve_wit_5_pure.
Axiom proof_of_all_prefixes_partial_solve_wit_5 : all_prefixes_partial_solve_wit_5.
Axiom proof_of_all_prefixes_partial_solve_wit_6 : all_prefixes_partial_solve_wit_6.
Axiom proof_of_all_prefixes_partial_solve_wit_7 : all_prefixes_partial_solve_wit_7.

End VC_Correct.
