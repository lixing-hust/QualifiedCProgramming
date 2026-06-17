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
Require Import coins_7.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import ptr_array2_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import ptr_array2_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_proof.
Require Import string_strategy_goal.
Require Import string_strategy_proof.

(*----- Function filter_by_substring -----*)

Definition filter_by_substring_safety_wit_1 := 
forall (substring_pre: Z) (strings_size_pre: Z) (strings_pre: Z) (substring_l: (@list Z)) (rows: (@list (@list Z))) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (substring_l)) + 1 ))) (PreH3 : (0 <= strings_size_pre)) (PreH4 : (strings_size_pre <= 100)) (PreH5 : (rows_well_formed_7 rows strings_size_pre )) (PreH6 : (valid_string substring_l )) (PreH7 : ((string_length (substring_l)) < INT_MAX)) (PreH8 : (problem_7_pre_z rows )) ,
  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (CharArray.full substring_pre ((string_length (substring_l)) + 1 ) (c_string (substring_l)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "substring" ) )) # Ptr  |-> substring_pre)
  **  ((( &( "strings_size" ) )) # Int  |-> strings_size_pre)
  **  ((( &( "strings" ) )) # Ptr  |-> strings_pre)
  **  (CharPtrArray2.full strings_pre strings_size_pre rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition filter_by_substring_safety_wit_2 := 
forall (substring_pre: Z) (strings_size_pre: Z) (strings_pre: Z) (substring_l: (@list Z)) (rows: (@list (@list Z))) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= ((string_length (substring_l)) + 1 ))) (PreH4 : (0 <= strings_size_pre)) (PreH5 : (strings_size_pre <= 100)) (PreH6 : (rows_well_formed_7 rows strings_size_pre )) (PreH7 : (valid_string substring_l )) (PreH8 : ((string_length (substring_l)) < INT_MAX)) (PreH9 : (problem_7_pre_z rows )) ,
  ((( &( "output_size" ) )) # Int  |->_)
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (PtrArray.undef_full retval_2 strings_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full substring_pre ((string_length (substring_l)) + 1 ) (c_string (substring_l)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "substring" ) )) # Ptr  |-> substring_pre)
  **  ((( &( "strings_size" ) )) # Int  |-> strings_size_pre)
  **  ((( &( "strings" ) )) # Ptr  |-> strings_pre)
  **  (CharPtrArray2.full strings_pre strings_size_pre rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition filter_by_substring_safety_wit_3 := 
forall (substring_pre: Z) (strings_size_pre: Z) (strings_pre: Z) (substring_l: (@list Z)) (rows: (@list (@list Z))) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= ((string_length (substring_l)) + 1 ))) (PreH4 : (0 <= strings_size_pre)) (PreH5 : (strings_size_pre <= 100)) (PreH6 : (rows_well_formed_7 rows strings_size_pre )) (PreH7 : (valid_string substring_l )) (PreH8 : ((string_length (substring_l)) < INT_MAX)) (PreH9 : (problem_7_pre_z rows )) ,
  ((( &( "cur" ) )) # Ptr  |->_)
  **  ((( &( "output_size" ) )) # Int  |-> 0)
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (PtrArray.undef_full retval_2 strings_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full substring_pre ((string_length (substring_l)) + 1 ) (c_string (substring_l)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "substring" ) )) # Ptr  |-> substring_pre)
  **  ((( &( "strings_size" ) )) # Int  |-> strings_size_pre)
  **  ((( &( "strings" ) )) # Ptr  |-> strings_pre)
  **  (CharPtrArray2.full strings_pre strings_size_pre rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition filter_by_substring_safety_wit_4 := 
forall (substring_pre: Z) (strings_size_pre: Z) (strings_pre: Z) (substring_l: (@list Z)) (rows: (@list (@list Z))) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= ((string_length (substring_l)) + 1 ))) (PreH4 : (0 <= strings_size_pre)) (PreH5 : (strings_size_pre <= 100)) (PreH6 : (rows_well_formed_7 rows strings_size_pre )) (PreH7 : (valid_string substring_l )) (PreH8 : ((string_length (substring_l)) < INT_MAX)) (PreH9 : (problem_7_pre_z rows )) ,
  ((( &( "hit" ) )) # Ptr  |->_)
  **  ((( &( "cur" ) )) # Ptr  |-> 0)
  **  ((( &( "output_size" ) )) # Int  |-> 0)
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (PtrArray.undef_full retval_2 strings_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full substring_pre ((string_length (substring_l)) + 1 ) (c_string (substring_l)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "substring" ) )) # Ptr  |-> substring_pre)
  **  ((( &( "strings_size" ) )) # Int  |-> strings_size_pre)
  **  ((( &( "strings" ) )) # Ptr  |-> strings_pre)
  **  (CharPtrArray2.full strings_pre strings_size_pre rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition filter_by_substring_safety_wit_5 := 
forall (substring_pre: Z) (strings_size_pre: Z) (strings_pre: Z) (substring_l: (@list Z)) (rows: (@list (@list Z))) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= ((string_length (substring_l)) + 1 ))) (PreH4 : (0 <= strings_size_pre)) (PreH5 : (strings_size_pre <= 100)) (PreH6 : (rows_well_formed_7 rows strings_size_pre )) (PreH7 : (valid_string substring_l )) (PreH8 : ((string_length (substring_l)) < INT_MAX)) (PreH9 : (problem_7_pre_z rows )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "hit" ) )) # Ptr  |-> 0)
  **  ((( &( "cur" ) )) # Ptr  |-> 0)
  **  ((( &( "output_size" ) )) # Int  |-> 0)
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (PtrArray.undef_full retval_2 strings_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full substring_pre ((string_length (substring_l)) + 1 ) (c_string (substring_l)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "substring" ) )) # Ptr  |-> substring_pre)
  **  ((( &( "strings_size" ) )) # Int  |-> strings_size_pre)
  **  ((( &( "strings" ) )) # Ptr  |-> strings_pre)
  **  (CharPtrArray2.full strings_pre strings_size_pre rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition filter_by_substring_safety_wit_6 := 
forall (substring_pre: Z) (strings_size_pre: Z) (strings_pre: Z) (substring_l: (@list Z)) (rows: (@list (@list Z))) (row_ptr: Z) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (i: Z) (output_size: Z) (out: Z) (data: Z) (retval: Z) (PreH1 : (strstr_result (row_payload_z_7 ((Znth (i) (rows) ((@nil Z))))) substring_l retval row_ptr )) (PreH2 : (0 <= ((string_length (substring_l)) + 1 ))) (PreH3 : (0 <= ((string_length ((row_payload_z_7 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) (PreH4 : (0 <= i)) (PreH5 : (i < strings_size_pre)) (PreH6 : (0 <= output_size)) (PreH7 : (output_size <= i)) (PreH8 : (output_size = (Zlength (output_rows)))) (PreH9 : (output_size = (Zlength (output_ptrs)))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (rows_well_formed_7 rows strings_size_pre )) (PreH13 : (valid_string substring_l )) (PreH14 : ((string_length (substring_l)) < INT_MAX)) (PreH15 : (problem_7_pre_z rows )) (PreH16 : (filter_substring_state_7 rows substring_l i output_rows )) (PreH17 : (valid_string (row_payload_z_7 ((Znth (i) (rows) ((@nil Z))))) )) (PreH18 : ((string_length ((row_payload_z_7 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX)) ,
  (store_string row_ptr (row_payload_z_7 ((Znth (i) (rows) ((@nil Z))))) )
  **  (store_string substring_pre substring_l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "strings_size" ) )) # Int  |-> strings_size_pre)
  **  ((( &( "strings" ) )) # Ptr  |-> strings_pre)
  **  ((( &( "substring" ) )) # Ptr  |-> substring_pre)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "hit" ) )) # Ptr  |-> retval)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.missing_i strings_pre strings_size_pre i row_ptr rows )
  **  (((strings_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size strings_size_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition filter_by_substring_safety_wit_7 := 
forall (substring_pre: Z) (strings_size_pre: Z) (strings_pre: Z) (substring_l: (@list Z)) (rows: (@list (@list Z))) (row_ptr: Z) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (i: Z) (output_size: Z) (hit: Z) (out: Z) (data: Z) (PreH1 : (0 <= ((string_length (substring_l)) + 1 ))) (PreH2 : (0 <= (Zlength ((Znth (i) (rows) ((@nil Z))))))) (PreH3 : (0 <= i)) (PreH4 : (i < strings_size_pre)) (PreH5 : (0 <= output_size)) (PreH6 : (output_size <= i)) (PreH7 : (output_size = (Zlength (output_rows)))) (PreH8 : (output_size = (Zlength (output_ptrs)))) (PreH9 : (hit <> 0)) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (rows_well_formed_7 rows strings_size_pre )) (PreH13 : (valid_string substring_l )) (PreH14 : ((string_length (substring_l)) < INT_MAX)) (PreH15 : (problem_7_pre_z rows )) (PreH16 : (filter_substring_state_7 rows substring_l i output_rows )) (PreH17 : (substring_match_z_7 (Znth (i) (rows) ((@nil Z))) substring_l )) ,
  (PtrArray.seg data 0 (output_size + 1 ) (app (output_ptrs) ((cons (row_ptr) ((@nil Z))))) )
  **  (PtrArray.undef_seg data (output_size + 1 ) strings_size_pre )
  **  (CharArray.full substring_pre ((string_length (substring_l)) + 1 ) (c_string (substring_l)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "strings_size" ) )) # Int  |-> strings_size_pre)
  **  ((( &( "strings" ) )) # Ptr  |-> strings_pre)
  **  ((( &( "substring" ) )) # Ptr  |-> substring_pre)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "hit" ) )) # Ptr  |-> hit)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.missing_i strings_pre strings_size_pre i row_ptr rows )
  **  (((strings_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
|--
  “ ((output_size + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (output_size + 1 )) ”
.

Definition filter_by_substring_safety_wit_8 := 
forall (substring_pre: Z) (strings_size_pre: Z) (strings_pre: Z) (substring_l: (@list Z)) (rows: (@list (@list Z))) (row_ptr: Z) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (i: Z) (output_size: Z) (hit: Z) (out: Z) (data: Z) (PreH1 : (0 <= ((string_length (substring_l)) + 1 ))) (PreH2 : (0 <= (Zlength ((Znth (i) (rows) ((@nil Z))))))) (PreH3 : (0 <= i)) (PreH4 : (i < strings_size_pre)) (PreH5 : (0 <= output_size)) (PreH6 : (output_size <= i)) (PreH7 : (output_size = (Zlength (output_rows)))) (PreH8 : (output_size = (Zlength (output_ptrs)))) (PreH9 : (hit <> 0)) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (rows_well_formed_7 rows strings_size_pre )) (PreH13 : (valid_string substring_l )) (PreH14 : ((string_length (substring_l)) < INT_MAX)) (PreH15 : (problem_7_pre_z rows )) (PreH16 : (filter_substring_state_7 rows substring_l i output_rows )) (PreH17 : (substring_match_z_7 (Znth (i) (rows) ((@nil Z))) substring_l )) ,
  (PtrArray.seg data 0 (output_size + 1 ) (app (output_ptrs) ((cons (row_ptr) ((@nil Z))))) )
  **  (PtrArray.undef_seg data (output_size + 1 ) strings_size_pre )
  **  (CharArray.full substring_pre ((string_length (substring_l)) + 1 ) (c_string (substring_l)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "strings_size" ) )) # Int  |-> strings_size_pre)
  **  ((( &( "strings" ) )) # Ptr  |-> strings_pre)
  **  ((( &( "substring" ) )) # Ptr  |-> substring_pre)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "hit" ) )) # Ptr  |-> hit)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.missing_i strings_pre strings_size_pre i row_ptr rows )
  **  (((strings_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition filter_by_substring_safety_wit_9 := 
forall (substring_pre: Z) (strings_size_pre: Z) (strings_pre: Z) (substring_l: (@list Z)) (rows: (@list (@list Z))) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (i: Z) (output_size: Z) (out: Z) (data: Z) (cur: Z) (hit: Z) (PreH1 : (0 <= i)) (PreH2 : (i < strings_size_pre)) (PreH3 : (0 <= output_size)) (PreH4 : (output_size <= (i + 1 ))) (PreH5 : (output_size = (Zlength (output_rows)))) (PreH6 : (output_size = (Zlength (output_ptrs)))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (hit <> 0)) (PreH10 : (rows_well_formed_7 rows strings_size_pre )) (PreH11 : (valid_string substring_l )) (PreH12 : ((string_length (substring_l)) < INT_MAX)) (PreH13 : (problem_7_pre_z rows )) (PreH14 : (filter_substring_state_7 rows substring_l (i + 1 ) output_rows )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "strings_size" ) )) # Int  |-> strings_size_pre)
  **  ((( &( "strings" ) )) # Ptr  |-> strings_pre)
  **  ((( &( "substring" ) )) # Ptr  |-> substring_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "hit" ) )) # Ptr  |-> hit)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.full strings_pre strings_size_pre rows )
  **  (store_string substring_pre substring_l )
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size strings_size_pre )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition filter_by_substring_safety_wit_10 := 
forall (substring_pre: Z) (strings_size_pre: Z) (strings_pre: Z) (substring_l: (@list Z)) (rows: (@list (@list Z))) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (i: Z) (output_size: Z) (out: Z) (data: Z) (cur: Z) (hit: Z) (PreH1 : (0 <= i)) (PreH2 : (i < strings_size_pre)) (PreH3 : (0 <= output_size)) (PreH4 : (output_size <= (i + 1 ))) (PreH5 : (output_size = (Zlength (output_rows)))) (PreH6 : (output_size = (Zlength (output_ptrs)))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (hit = 0)) (PreH10 : (rows_well_formed_7 rows strings_size_pre )) (PreH11 : (valid_string substring_l )) (PreH12 : ((string_length (substring_l)) < INT_MAX)) (PreH13 : (problem_7_pre_z rows )) (PreH14 : (filter_substring_state_7 rows substring_l (i + 1 ) output_rows )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "strings_size" ) )) # Int  |-> strings_size_pre)
  **  ((( &( "strings" ) )) # Ptr  |-> strings_pre)
  **  ((( &( "substring" ) )) # Ptr  |-> substring_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "hit" ) )) # Ptr  |-> hit)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.full strings_pre strings_size_pre rows )
  **  (store_string substring_pre substring_l )
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size strings_size_pre )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition filter_by_substring_entail_wit_1 := 
(
forall (substring_pre: Z) (strings_size_pre: Z) (strings_pre: Z) (substring_l: (@list Z)) (rows: (@list (@list Z))) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= ((string_length (substring_l)) + 1 ))) (PreH4 : (0 <= strings_size_pre)) (PreH5 : (strings_size_pre <= 100)) (PreH6 : (rows_well_formed_7 rows strings_size_pre )) (PreH7 : (valid_string substring_l )) (PreH8 : ((string_length (substring_l)) < INT_MAX)) (PreH9 : (problem_7_pre_z rows )) ,
  (PtrArray.undef_full retval_2 strings_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full substring_pre ((string_length (substring_l)) + 1 ) (c_string (substring_l)) )
  **  (CharPtrArray2.full strings_pre strings_size_pre rows )
|--
  EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= strings_size_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 = (Zlength (output_rows))) ” 
  &&  “ (0 = (Zlength (output_ptrs))) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (rows_well_formed_7 rows strings_size_pre ) ” 
  &&  “ (valid_string substring_l ) ” 
  &&  “ ((string_length (substring_l)) < INT_MAX) ” 
  &&  “ (problem_7_pre_z rows ) ” 
  &&  “ (filter_substring_state_7 rows substring_l 0 output_rows ) ”
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.full strings_pre strings_size_pre rows )
  **  (store_string substring_pre substring_l )
  **  (PtrArray.seg retval_2 0 0 output_ptrs )
  **  (PtrArray.undef_seg retval_2 0 strings_size_pre )
) \/
(
forall (strings_size_pre: Z) (substring_l: (@list Z)) (rows: (@list (@list Z))) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= ((string_length (substring_l)) + 1 ))) (PreH4 : (0 <= strings_size_pre)) (PreH5 : (strings_size_pre <= 100)) (PreH6 : (rows_well_formed_7 rows strings_size_pre )) (PreH7 : (valid_string substring_l )) (PreH8 : ((string_length (substring_l)) < INT_MAX)) (PreH9 : (problem_7_pre_z rows )) ,
  TT && emp 
|--
  EX (output_rows: (@list (@list Z))) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= strings_size_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 = (Zlength (output_rows))) ” 
  &&  “ (0 = (Zlength ((@nil Z)))) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (rows_well_formed_7 rows strings_size_pre ) ” 
  &&  “ (valid_string substring_l ) ” 
  &&  “ ((string_length (substring_l)) < INT_MAX) ” 
  &&  “ (problem_7_pre_z rows ) ” 
  &&  “ (filter_substring_state_7 rows substring_l 0 output_rows ) ”
  &&  emp
).

Definition filter_by_substring_entail_wit_2 := 
(
forall (substring_pre: Z) (strings_size_pre: Z) (strings_pre: Z) (substring_l: (@list Z)) (rows: (@list (@list Z))) (data: Z) (out: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (output_size: Z) (i: Z) (PreH1 : (i < strings_size_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= strings_size_pre)) (PreH4 : (0 <= output_size)) (PreH5 : (output_size <= i)) (PreH6 : (output_size = (Zlength (output_rows_2)))) (PreH7 : (output_size = (Zlength (output_ptrs_2)))) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (rows_well_formed_7 rows strings_size_pre )) (PreH11 : (valid_string substring_l )) (PreH12 : ((string_length (substring_l)) < INT_MAX)) (PreH13 : (problem_7_pre_z rows )) (PreH14 : (filter_substring_state_7 rows substring_l i output_rows_2 )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.full strings_pre strings_size_pre rows )
  **  (store_string substring_pre substring_l )
  **  (PtrArray.seg data 0 output_size output_ptrs_2 )
  **  (PtrArray.undef_seg data output_size strings_size_pre )
|--
  EX (row_ptr: Z)  (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
  “ (0 <= i) ” 
  &&  “ (i < strings_size_pre) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= i) ” 
  &&  “ (output_size = (Zlength (output_rows))) ” 
  &&  “ (output_size = (Zlength (output_ptrs))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (rows_well_formed_7 rows strings_size_pre ) ” 
  &&  “ (valid_string substring_l ) ” 
  &&  “ ((string_length (substring_l)) < INT_MAX) ” 
  &&  “ (problem_7_pre_z rows ) ” 
  &&  “ (filter_substring_state_7 rows substring_l i output_rows ) ” 
  &&  “ (valid_string (row_payload_z_7 ((Znth (i) (rows) ((@nil Z))))) ) ” 
  &&  “ ((string_length ((row_payload_z_7 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX) ” 
  &&  “ ((Zlength ((Znth (i) (rows) ((@nil Z))))) = ((string_length ((row_payload_z_7 ((Znth (i) (rows) ((@nil Z))))))) + 1 )) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.missing_i strings_pre strings_size_pre i row_ptr rows )
  **  (((strings_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_7 ((Znth (i) (rows) ((@nil Z))))) )
  **  (store_string substring_pre substring_l )
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size strings_size_pre )
) \/
(
forall (strings_size_pre: Z) (substring_l: (@list Z)) (rows: (@list (@list Z))) (data: Z) (out: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (output_size: Z) (i: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (0 <= ((string_length (substring_l)) + 1 ))) (PreH2 : (0 <= (Zlength ((Znth i rows __default__List_Z))))) (PreH3 : (i < strings_size_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= strings_size_pre)) (PreH6 : (0 <= output_size)) (PreH7 : (output_size <= i)) (PreH8 : (output_size = (Zlength (output_rows_2)))) (PreH9 : (output_size = (Zlength (output_ptrs_2)))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (rows_well_formed_7 rows strings_size_pre )) (PreH13 : (valid_string substring_l )) (PreH14 : ((string_length (substring_l)) < INT_MAX)) (PreH15 : (problem_7_pre_z rows )) (PreH16 : (filter_substring_state_7 rows substring_l i output_rows_2 )) ,
  (CharArray.full row_ptr_2 (Zlength ((Znth i rows __default__List_Z))) (Znth i rows __default__List_Z) )
|--
  EX (output_rows: (@list (@list Z))) ,
  “ (0 <= i) ” 
  &&  “ (i < strings_size_pre) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= i) ” 
  &&  “ (output_size = (Zlength (output_rows))) ” 
  &&  “ (output_size = (Zlength (output_ptrs_2))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (rows_well_formed_7 rows strings_size_pre ) ” 
  &&  “ (valid_string substring_l ) ” 
  &&  “ ((string_length (substring_l)) < INT_MAX) ” 
  &&  “ (problem_7_pre_z rows ) ” 
  &&  “ (filter_substring_state_7 rows substring_l i output_rows ) ” 
  &&  “ (valid_string (row_payload_z_7 ((Znth (i) (rows) ((@nil Z))))) ) ” 
  &&  “ ((string_length ((row_payload_z_7 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX) ” 
  &&  “ ((Zlength ((Znth (i) (rows) ((@nil Z))))) = ((string_length ((row_payload_z_7 ((Znth (i) (rows) ((@nil Z))))))) + 1 )) ”
  &&  (CharArray.full row_ptr_2 ((string_length ((row_payload_z_7 ((Znth (i) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_7 ((Znth (i) (rows) ((@nil Z))))))) )
).

Definition filter_by_substring_entail_wit_3 := 
forall (substring_pre: Z) (strings_size_pre: Z) (strings_pre: Z) (substring_l: (@list Z)) (rows: (@list (@list Z))) (row_ptr: Z) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (i: Z) (output_size: Z) (out: Z) (data: Z) (PreH1 : (0 <= i)) (PreH2 : (i < strings_size_pre)) (PreH3 : (0 <= output_size)) (PreH4 : (output_size <= i)) (PreH5 : (output_size = (Zlength (output_rows_2)))) (PreH6 : (output_size = (Zlength (output_ptrs_2)))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (rows_well_formed_7 rows strings_size_pre )) (PreH10 : (valid_string substring_l )) (PreH11 : ((string_length (substring_l)) < INT_MAX)) (PreH12 : (problem_7_pre_z rows )) (PreH13 : (filter_substring_state_7 rows substring_l i output_rows_2 )) (PreH14 : (valid_string (row_payload_z_7 ((Znth (i) (rows) ((@nil Z))))) )) (PreH15 : ((string_length ((row_payload_z_7 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX)) (PreH16 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = ((string_length ((row_payload_z_7 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.missing_i strings_pre strings_size_pre i row_ptr rows )
  **  (((strings_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_7 ((Znth (i) (rows) ((@nil Z))))) )
  **  (store_string substring_pre substring_l )
  **  (PtrArray.seg data 0 output_size output_ptrs_2 )
  **  (PtrArray.undef_seg data output_size strings_size_pre )
|--
  EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
  “ (0 <= i) ” 
  &&  “ (i < strings_size_pre) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= i) ” 
  &&  “ (output_size = (Zlength (output_rows))) ” 
  &&  “ (output_size = (Zlength (output_ptrs))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (rows_well_formed_7 rows strings_size_pre ) ” 
  &&  “ (valid_string substring_l ) ” 
  &&  “ ((string_length (substring_l)) < INT_MAX) ” 
  &&  “ (problem_7_pre_z rows ) ” 
  &&  “ (filter_substring_state_7 rows substring_l i output_rows ) ” 
  &&  “ (valid_string (row_payload_z_7 ((Znth (i) (rows) ((@nil Z))))) ) ” 
  &&  “ ((string_length ((row_payload_z_7 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.missing_i strings_pre strings_size_pre i row_ptr rows )
  **  (((strings_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_7 ((Znth (i) (rows) ((@nil Z))))) )
  **  (store_string substring_pre substring_l )
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size strings_size_pre )
.

Definition filter_by_substring_entail_wit_4 := 
(
forall (substring_pre: Z) (strings_size_pre: Z) (strings_pre: Z) (substring_l: (@list Z)) (rows: (@list (@list Z))) (row_ptr: Z) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (i: Z) (output_size: Z) (out: Z) (data: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (strstr_result (row_payload_z_7 ((Znth (i) (rows) ((@nil Z))))) substring_l retval row_ptr )) (PreH3 : (0 <= ((string_length (substring_l)) + 1 ))) (PreH4 : (0 <= ((string_length ((row_payload_z_7 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) (PreH5 : (0 <= i)) (PreH6 : (i < strings_size_pre)) (PreH7 : (0 <= output_size)) (PreH8 : (output_size <= i)) (PreH9 : (output_size = (Zlength (output_rows_2)))) (PreH10 : (output_size = (Zlength (output_ptrs_2)))) (PreH11 : (out <> 0)) (PreH12 : (data <> 0)) (PreH13 : (rows_well_formed_7 rows strings_size_pre )) (PreH14 : (valid_string substring_l )) (PreH15 : ((string_length (substring_l)) < INT_MAX)) (PreH16 : (problem_7_pre_z rows )) (PreH17 : (filter_substring_state_7 rows substring_l i output_rows_2 )) (PreH18 : (valid_string (row_payload_z_7 ((Znth (i) (rows) ((@nil Z))))) )) (PreH19 : ((string_length ((row_payload_z_7 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX)) ,
  (store_string row_ptr (row_payload_z_7 ((Znth (i) (rows) ((@nil Z))))) )
  **  (store_string substring_pre substring_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.missing_i strings_pre strings_size_pre i row_ptr rows )
  **  (((strings_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (PtrArray.seg data 0 output_size output_ptrs_2 )
  **  (PtrArray.undef_seg data output_size strings_size_pre )
|--
  EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
  “ (0 <= i) ” 
  &&  “ (i < strings_size_pre) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= i) ” 
  &&  “ (output_size = (Zlength (output_rows))) ” 
  &&  “ (output_size = (Zlength (output_ptrs))) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (rows_well_formed_7 rows strings_size_pre ) ” 
  &&  “ (valid_string substring_l ) ” 
  &&  “ ((string_length (substring_l)) < INT_MAX) ” 
  &&  “ (problem_7_pre_z rows ) ” 
  &&  “ (filter_substring_state_7 rows substring_l i output_rows ) ” 
  &&  “ (substring_match_z_7 (Znth (i) (rows) ((@nil Z))) substring_l ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.missing_i strings_pre strings_size_pre i row_ptr rows )
  **  (((strings_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
  **  (store_string substring_pre substring_l )
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size strings_size_pre )
) \/
(
forall (strings_size_pre: Z) (substring_l: (@list Z)) (rows: (@list (@list Z))) (row_ptr: Z) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (i: Z) (output_size: Z) (out: Z) (data: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (strstr_result (row_payload_z_7 ((Znth (i) (rows) ((@nil Z))))) substring_l retval row_ptr )) (PreH3 : (0 <= ((string_length (substring_l)) + 1 ))) (PreH4 : (0 <= ((string_length ((row_payload_z_7 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) (PreH5 : (0 <= i)) (PreH6 : (i < strings_size_pre)) (PreH7 : (0 <= output_size)) (PreH8 : (output_size <= i)) (PreH9 : (output_size = (Zlength (output_rows_2)))) (PreH10 : (output_size = (Zlength (output_ptrs_2)))) (PreH11 : (out <> 0)) (PreH12 : (data <> 0)) (PreH13 : (rows_well_formed_7 rows strings_size_pre )) (PreH14 : (valid_string substring_l )) (PreH15 : ((string_length (substring_l)) < INT_MAX)) (PreH16 : (problem_7_pre_z rows )) (PreH17 : (filter_substring_state_7 rows substring_l i output_rows_2 )) (PreH18 : (valid_string (row_payload_z_7 ((Znth (i) (rows) ((@nil Z))))) )) (PreH19 : ((string_length ((row_payload_z_7 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX)) ,
  (CharArray.full row_ptr ((string_length ((row_payload_z_7 ((Znth (i) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_7 ((Znth (i) (rows) ((@nil Z))))))) )
|--
  EX (output_rows: (@list (@list Z))) ,
  “ (0 <= i) ” 
  &&  “ (i < strings_size_pre) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= i) ” 
  &&  “ (output_size = (Zlength (output_rows))) ” 
  &&  “ (output_size = (Zlength (output_ptrs_2))) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (rows_well_formed_7 rows strings_size_pre ) ” 
  &&  “ (valid_string substring_l ) ” 
  &&  “ ((string_length (substring_l)) < INT_MAX) ” 
  &&  “ (problem_7_pre_z rows ) ” 
  &&  “ (filter_substring_state_7 rows substring_l i output_rows ) ” 
  &&  “ (substring_match_z_7 (Znth (i) (rows) ((@nil Z))) substring_l ) ”
  &&  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
).

Definition filter_by_substring_entail_wit_5 := 
(
forall (substring_pre: Z) (strings_size_pre: Z) (strings_pre: Z) (substring_l: (@list Z)) (rows: (@list (@list Z))) (row_ptr: Z) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (i: Z) (output_size: Z) (hit: Z) (out: Z) (data: Z) (PreH1 : (0 <= ((string_length (substring_l)) + 1 ))) (PreH2 : (0 <= (Zlength ((Znth (i) (rows) ((@nil Z))))))) (PreH3 : (0 <= i)) (PreH4 : (i < strings_size_pre)) (PreH5 : (0 <= output_size)) (PreH6 : (output_size <= i)) (PreH7 : (output_size = (Zlength (output_rows_2)))) (PreH8 : (output_size = (Zlength (output_ptrs_2)))) (PreH9 : (hit <> 0)) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (rows_well_formed_7 rows strings_size_pre )) (PreH13 : (valid_string substring_l )) (PreH14 : ((string_length (substring_l)) < INT_MAX)) (PreH15 : (problem_7_pre_z rows )) (PreH16 : (filter_substring_state_7 rows substring_l i output_rows_2 )) (PreH17 : (substring_match_z_7 (Znth (i) (rows) ((@nil Z))) substring_l )) ,
  (PtrArray.seg data 0 (output_size + 1 ) (app (output_ptrs_2) ((cons (row_ptr) ((@nil Z))))) )
  **  (PtrArray.undef_seg data (output_size + 1 ) strings_size_pre )
  **  (CharArray.full substring_pre ((string_length (substring_l)) + 1 ) (c_string (substring_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.missing_i strings_pre strings_size_pre i row_ptr rows )
  **  (((strings_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
|--
  EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
  “ (0 <= i) ” 
  &&  “ (i < strings_size_pre) ” 
  &&  “ (0 <= (output_size + 1 )) ” 
  &&  “ ((output_size + 1 ) <= (i + 1 )) ” 
  &&  “ ((output_size + 1 ) = (Zlength (output_rows))) ” 
  &&  “ ((output_size + 1 ) = (Zlength (output_ptrs))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (hit <> 0) ” 
  &&  “ (rows_well_formed_7 rows strings_size_pre ) ” 
  &&  “ (valid_string substring_l ) ” 
  &&  “ ((string_length (substring_l)) < INT_MAX) ” 
  &&  “ (problem_7_pre_z rows ) ” 
  &&  “ (filter_substring_state_7 rows substring_l (i + 1 ) output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.full strings_pre strings_size_pre rows )
  **  (store_string substring_pre substring_l )
  **  (PtrArray.seg data 0 (output_size + 1 ) output_ptrs )
  **  (PtrArray.undef_seg data (output_size + 1 ) strings_size_pre )
) \/
(
forall (strings_size_pre: Z) (strings_pre: Z) (substring_l: (@list Z)) (rows: (@list (@list Z))) (row_ptr: Z) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (i: Z) (output_size: Z) (hit: Z) (out: Z) (data: Z) (PreH1 : (0 <= ((string_length (substring_l)) + 1 ))) (PreH2 : (0 <= (Zlength ((Znth (i) (rows) ((@nil Z))))))) (PreH3 : (0 <= i)) (PreH4 : (i < strings_size_pre)) (PreH5 : (0 <= output_size)) (PreH6 : (output_size <= i)) (PreH7 : (output_size = (Zlength (output_rows_2)))) (PreH8 : (output_size = (Zlength (output_ptrs_2)))) (PreH9 : (hit <> 0)) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (rows_well_formed_7 rows strings_size_pre )) (PreH13 : (valid_string substring_l )) (PreH14 : ((string_length (substring_l)) < INT_MAX)) (PreH15 : (problem_7_pre_z rows )) (PreH16 : (filter_substring_state_7 rows substring_l i output_rows_2 )) (PreH17 : (substring_match_z_7 (Znth (i) (rows) ((@nil Z))) substring_l )) ,
  (CharPtrArray2.missing_i strings_pre strings_size_pre i row_ptr rows )
  **  (((strings_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
|--
  EX (output_rows: (@list (@list Z))) ,
  “ (0 <= i) ” 
  &&  “ (i < strings_size_pre) ” 
  &&  “ (0 <= (output_size + 1 )) ” 
  &&  “ ((output_size + 1 ) <= (i + 1 )) ” 
  &&  “ ((output_size + 1 ) = (Zlength (output_rows))) ” 
  &&  “ ((output_size + 1 ) = (Zlength ((app (output_ptrs_2) ((cons (row_ptr) ((@nil Z)))))))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (hit <> 0) ” 
  &&  “ (rows_well_formed_7 rows strings_size_pre ) ” 
  &&  “ (valid_string substring_l ) ” 
  &&  “ ((string_length (substring_l)) < INT_MAX) ” 
  &&  “ (problem_7_pre_z rows ) ” 
  &&  “ (filter_substring_state_7 rows substring_l (i + 1 ) output_rows ) ”
  &&  (CharPtrArray2.full strings_pre strings_size_pre rows )
).

Definition filter_by_substring_entail_wit_6 := 
(
forall (substring_pre: Z) (strings_size_pre: Z) (strings_pre: Z) (substring_l: (@list Z)) (rows: (@list (@list Z))) (row_ptr: Z) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (i: Z) (output_size: Z) (out: Z) (data: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (strstr_result (row_payload_z_7 ((Znth (i) (rows) ((@nil Z))))) substring_l retval row_ptr )) (PreH3 : (0 <= ((string_length (substring_l)) + 1 ))) (PreH4 : (0 <= ((string_length ((row_payload_z_7 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) (PreH5 : (0 <= i)) (PreH6 : (i < strings_size_pre)) (PreH7 : (0 <= output_size)) (PreH8 : (output_size <= i)) (PreH9 : (output_size = (Zlength (output_rows_2)))) (PreH10 : (output_size = (Zlength (output_ptrs_2)))) (PreH11 : (out <> 0)) (PreH12 : (data <> 0)) (PreH13 : (rows_well_formed_7 rows strings_size_pre )) (PreH14 : (valid_string substring_l )) (PreH15 : ((string_length (substring_l)) < INT_MAX)) (PreH16 : (problem_7_pre_z rows )) (PreH17 : (filter_substring_state_7 rows substring_l i output_rows_2 )) (PreH18 : (valid_string (row_payload_z_7 ((Znth (i) (rows) ((@nil Z))))) )) (PreH19 : ((string_length ((row_payload_z_7 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX)) ,
  (store_string row_ptr (row_payload_z_7 ((Znth (i) (rows) ((@nil Z))))) )
  **  (store_string substring_pre substring_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.missing_i strings_pre strings_size_pre i row_ptr rows )
  **  (((strings_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (PtrArray.seg data 0 output_size output_ptrs_2 )
  **  (PtrArray.undef_seg data output_size strings_size_pre )
|--
  EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
  “ (0 <= i) ” 
  &&  “ (i < strings_size_pre) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= i) ” 
  &&  “ (output_size = (Zlength (output_rows))) ” 
  &&  “ (output_size = (Zlength (output_ptrs))) ” 
  &&  “ (retval = 0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (rows_well_formed_7 rows strings_size_pre ) ” 
  &&  “ (valid_string substring_l ) ” 
  &&  “ ((string_length (substring_l)) < INT_MAX) ” 
  &&  “ (problem_7_pre_z rows ) ” 
  &&  “ (filter_substring_state_7 rows substring_l i output_rows ) ” 
  &&  “ ~((substring_match_z_7 (Znth (i) (rows) ((@nil Z))) substring_l )) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.missing_i strings_pre strings_size_pre i row_ptr rows )
  **  (((strings_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
  **  (store_string substring_pre substring_l )
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size strings_size_pre )
) \/
(
forall (strings_size_pre: Z) (substring_l: (@list Z)) (rows: (@list (@list Z))) (row_ptr: Z) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (i: Z) (output_size: Z) (out: Z) (data: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (strstr_result (row_payload_z_7 ((Znth (i) (rows) ((@nil Z))))) substring_l retval row_ptr )) (PreH3 : (0 <= ((string_length (substring_l)) + 1 ))) (PreH4 : (0 <= ((string_length ((row_payload_z_7 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) (PreH5 : (0 <= i)) (PreH6 : (i < strings_size_pre)) (PreH7 : (0 <= output_size)) (PreH8 : (output_size <= i)) (PreH9 : (output_size = (Zlength (output_rows_2)))) (PreH10 : (output_size = (Zlength (output_ptrs_2)))) (PreH11 : (out <> 0)) (PreH12 : (data <> 0)) (PreH13 : (rows_well_formed_7 rows strings_size_pre )) (PreH14 : (valid_string substring_l )) (PreH15 : ((string_length (substring_l)) < INT_MAX)) (PreH16 : (problem_7_pre_z rows )) (PreH17 : (filter_substring_state_7 rows substring_l i output_rows_2 )) (PreH18 : (valid_string (row_payload_z_7 ((Znth (i) (rows) ((@nil Z))))) )) (PreH19 : ((string_length ((row_payload_z_7 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX)) ,
  (CharArray.full row_ptr ((string_length ((row_payload_z_7 ((Znth (i) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_7 ((Znth (i) (rows) ((@nil Z))))))) )
|--
  EX (output_rows: (@list (@list Z))) ,
  “ (0 <= i) ” 
  &&  “ (i < strings_size_pre) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= i) ” 
  &&  “ (output_size = (Zlength (output_rows))) ” 
  &&  “ (output_size = (Zlength (output_ptrs_2))) ” 
  &&  “ (retval = 0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (rows_well_formed_7 rows strings_size_pre ) ” 
  &&  “ (valid_string substring_l ) ” 
  &&  “ ((string_length (substring_l)) < INT_MAX) ” 
  &&  “ (problem_7_pre_z rows ) ” 
  &&  “ (filter_substring_state_7 rows substring_l i output_rows ) ” 
  &&  “ ~((substring_match_z_7 (Znth (i) (rows) ((@nil Z))) substring_l )) ”
  &&  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
).

Definition filter_by_substring_entail_wit_7 := 
(
forall (substring_pre: Z) (strings_size_pre: Z) (strings_pre: Z) (substring_l: (@list Z)) (rows: (@list (@list Z))) (row_ptr: Z) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (i: Z) (output_size: Z) (hit: Z) (out: Z) (data: Z) (PreH1 : (0 <= i)) (PreH2 : (i < strings_size_pre)) (PreH3 : (0 <= output_size)) (PreH4 : (output_size <= i)) (PreH5 : (output_size = (Zlength (output_rows_2)))) (PreH6 : (output_size = (Zlength (output_ptrs_2)))) (PreH7 : (hit = 0)) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (rows_well_formed_7 rows strings_size_pre )) (PreH11 : (valid_string substring_l )) (PreH12 : ((string_length (substring_l)) < INT_MAX)) (PreH13 : (problem_7_pre_z rows )) (PreH14 : (filter_substring_state_7 rows substring_l i output_rows_2 )) (PreH15 : ~((substring_match_z_7 (Znth (i) (rows) ((@nil Z))) substring_l ))) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.missing_i strings_pre strings_size_pre i row_ptr rows )
  **  (((strings_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
  **  (store_string substring_pre substring_l )
  **  (PtrArray.seg data 0 output_size output_ptrs_2 )
  **  (PtrArray.undef_seg data output_size strings_size_pre )
|--
  EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
  “ (0 <= i) ” 
  &&  “ (i < strings_size_pre) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= (i + 1 )) ” 
  &&  “ (output_size = (Zlength (output_rows))) ” 
  &&  “ (output_size = (Zlength (output_ptrs))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (hit = 0) ” 
  &&  “ (rows_well_formed_7 rows strings_size_pre ) ” 
  &&  “ (valid_string substring_l ) ” 
  &&  “ ((string_length (substring_l)) < INT_MAX) ” 
  &&  “ (problem_7_pre_z rows ) ” 
  &&  “ (filter_substring_state_7 rows substring_l (i + 1 ) output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.full strings_pre strings_size_pre rows )
  **  (store_string substring_pre substring_l )
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size strings_size_pre )
) \/
(
forall (strings_size_pre: Z) (strings_pre: Z) (substring_l: (@list Z)) (rows: (@list (@list Z))) (row_ptr: Z) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (i: Z) (output_size: Z) (hit: Z) (out: Z) (data: Z) (PreH1 : (0 <= ((string_length (substring_l)) + 1 ))) (PreH2 : (0 <= (Zlength ((Znth (i) (rows) ((@nil Z))))))) (PreH3 : (0 <= i)) (PreH4 : (i < strings_size_pre)) (PreH5 : (0 <= output_size)) (PreH6 : (output_size <= i)) (PreH7 : (output_size = (Zlength (output_rows_2)))) (PreH8 : (output_size = (Zlength (output_ptrs_2)))) (PreH9 : (hit = 0)) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (rows_well_formed_7 rows strings_size_pre )) (PreH13 : (valid_string substring_l )) (PreH14 : ((string_length (substring_l)) < INT_MAX)) (PreH15 : (problem_7_pre_z rows )) (PreH16 : (filter_substring_state_7 rows substring_l i output_rows_2 )) (PreH17 : ~((substring_match_z_7 (Znth (i) (rows) ((@nil Z))) substring_l ))) ,
  (CharPtrArray2.missing_i strings_pre strings_size_pre i row_ptr rows )
  **  (((strings_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
|--
  EX (output_rows: (@list (@list Z))) ,
  “ (0 <= i) ” 
  &&  “ (i < strings_size_pre) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= (i + 1 )) ” 
  &&  “ (output_size = (Zlength (output_rows))) ” 
  &&  “ (output_size = (Zlength (output_ptrs_2))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (hit = 0) ” 
  &&  “ (rows_well_formed_7 rows strings_size_pre ) ” 
  &&  “ (valid_string substring_l ) ” 
  &&  “ ((string_length (substring_l)) < INT_MAX) ” 
  &&  “ (problem_7_pre_z rows ) ” 
  &&  “ (filter_substring_state_7 rows substring_l (i + 1 ) output_rows ) ”
  &&  (CharPtrArray2.full strings_pre strings_size_pre rows )
).

Definition filter_by_substring_entail_wit_8_1 := 
forall (substring_pre: Z) (strings_size_pre: Z) (strings_pre: Z) (substring_l: (@list Z)) (rows: (@list (@list Z))) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (i: Z) (output_size: Z) (out: Z) (data: Z) (hit: Z) (PreH1 : (0 <= i)) (PreH2 : (i < strings_size_pre)) (PreH3 : (0 <= output_size)) (PreH4 : (output_size <= (i + 1 ))) (PreH5 : (output_size = (Zlength (output_rows_2)))) (PreH6 : (output_size = (Zlength (output_ptrs_2)))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (hit <> 0)) (PreH10 : (rows_well_formed_7 rows strings_size_pre )) (PreH11 : (valid_string substring_l )) (PreH12 : ((string_length (substring_l)) < INT_MAX)) (PreH13 : (problem_7_pre_z rows )) (PreH14 : (filter_substring_state_7 rows substring_l (i + 1 ) output_rows_2 )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.full strings_pre strings_size_pre rows )
  **  (store_string substring_pre substring_l )
  **  (PtrArray.seg data 0 output_size output_ptrs_2 )
  **  (PtrArray.undef_seg data output_size strings_size_pre )
|--
  EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= strings_size_pre) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= (i + 1 )) ” 
  &&  “ (output_size = (Zlength (output_rows))) ” 
  &&  “ (output_size = (Zlength (output_ptrs))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (rows_well_formed_7 rows strings_size_pre ) ” 
  &&  “ (valid_string substring_l ) ” 
  &&  “ ((string_length (substring_l)) < INT_MAX) ” 
  &&  “ (problem_7_pre_z rows ) ” 
  &&  “ (filter_substring_state_7 rows substring_l (i + 1 ) output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.full strings_pre strings_size_pre rows )
  **  (store_string substring_pre substring_l )
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size strings_size_pre )
.

Definition filter_by_substring_entail_wit_8_2 := 
forall (substring_pre: Z) (strings_size_pre: Z) (strings_pre: Z) (substring_l: (@list Z)) (rows: (@list (@list Z))) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (i: Z) (output_size: Z) (out: Z) (data: Z) (hit: Z) (PreH1 : (0 <= i)) (PreH2 : (i < strings_size_pre)) (PreH3 : (0 <= output_size)) (PreH4 : (output_size <= (i + 1 ))) (PreH5 : (output_size = (Zlength (output_rows_2)))) (PreH6 : (output_size = (Zlength (output_ptrs_2)))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (hit = 0)) (PreH10 : (rows_well_formed_7 rows strings_size_pre )) (PreH11 : (valid_string substring_l )) (PreH12 : ((string_length (substring_l)) < INT_MAX)) (PreH13 : (problem_7_pre_z rows )) (PreH14 : (filter_substring_state_7 rows substring_l (i + 1 ) output_rows_2 )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.full strings_pre strings_size_pre rows )
  **  (store_string substring_pre substring_l )
  **  (PtrArray.seg data 0 output_size output_ptrs_2 )
  **  (PtrArray.undef_seg data output_size strings_size_pre )
|--
  EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= strings_size_pre) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= (i + 1 )) ” 
  &&  “ (output_size = (Zlength (output_rows))) ” 
  &&  “ (output_size = (Zlength (output_ptrs))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (rows_well_formed_7 rows strings_size_pre ) ” 
  &&  “ (valid_string substring_l ) ” 
  &&  “ ((string_length (substring_l)) < INT_MAX) ” 
  &&  “ (problem_7_pre_z rows ) ” 
  &&  “ (filter_substring_state_7 rows substring_l (i + 1 ) output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.full strings_pre strings_size_pre rows )
  **  (store_string substring_pre substring_l )
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size strings_size_pre )
.

Definition filter_by_substring_return_wit_1 := 
(
forall (substring_pre: Z) (strings_size_pre: Z) (strings_pre: Z) (substring_l: (@list Z)) (rows: (@list (@list Z))) (data_2: Z) (out: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (output_size_2: Z) (i: Z) (PreH1 : (i >= strings_size_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= strings_size_pre)) (PreH4 : (0 <= output_size_2)) (PreH5 : (output_size_2 <= i)) (PreH6 : (output_size_2 = (Zlength (output_rows_2)))) (PreH7 : (output_size_2 = (Zlength (output_ptrs_2)))) (PreH8 : (out <> 0)) (PreH9 : (data_2 <> 0)) (PreH10 : (rows_well_formed_7 rows strings_size_pre )) (PreH11 : (valid_string substring_l )) (PreH12 : ((string_length (substring_l)) < INT_MAX)) (PreH13 : (problem_7_pre_z rows )) (PreH14 : (filter_substring_state_7 rows substring_l i output_rows_2 )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data_2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size_2)
  **  (CharPtrArray2.full strings_pre strings_size_pre rows )
  **  (store_string substring_pre substring_l )
  **  (PtrArray.seg data_2 0 output_size_2 output_ptrs_2 )
  **  (PtrArray.undef_seg data_2 output_size_2 strings_size_pre )
|--
  EX (data: Z)  (output_ptrs: (@list Z))  (output_rows: (@list (@list Z)))  (output_size: Z) ,
  “ (out <> 0) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= strings_size_pre) ” 
  &&  “ (output_size = (Zlength (output_rows))) ” 
  &&  “ (output_size = (Zlength (output_ptrs))) ” 
  &&  “ (problem_7_spec_z rows substring_l output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (CharPtrArray2.full strings_pre strings_size_pre rows )
  **  (store_string substring_pre substring_l )
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size strings_size_pre )
) \/
(
forall (strings_size_pre: Z) (substring_l: (@list Z)) (rows: (@list (@list Z))) (data_2: Z) (out: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (output_size_2: Z) (i: Z) (PreH1 : (0 <= ((string_length (substring_l)) + 1 ))) (PreH2 : (i >= strings_size_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= strings_size_pre)) (PreH5 : (0 <= output_size_2)) (PreH6 : (output_size_2 <= i)) (PreH7 : (output_size_2 = (Zlength (output_rows_2)))) (PreH8 : (output_size_2 = (Zlength (output_ptrs_2)))) (PreH9 : (out <> 0)) (PreH10 : (data_2 <> 0)) (PreH11 : (rows_well_formed_7 rows strings_size_pre )) (PreH12 : (valid_string substring_l )) (PreH13 : ((string_length (substring_l)) < INT_MAX)) (PreH14 : (problem_7_pre_z rows )) (PreH15 : (filter_substring_state_7 rows substring_l i output_rows_2 )) ,
  (PtrArray.seg data_2 0 output_size_2 output_ptrs_2 )
  **  (PtrArray.undef_seg data_2 output_size_2 strings_size_pre )
|--
  EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
  “ (output_size_2 = (Zlength (output_rows))) ” 
  &&  “ (output_size_2 = (Zlength (output_rows))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (0 <= (Zlength (output_rows))) ” 
  &&  “ ((Zlength (output_rows)) <= strings_size_pre) ” 
  &&  “ ((Zlength (output_rows)) = (Zlength (output_ptrs))) ” 
  &&  “ (problem_7_spec_z rows substring_l output_rows ) ”
  &&  (PtrArray.seg data_2 0 (Zlength (output_rows)) output_ptrs )
  **  (PtrArray.undef_seg data_2 (Zlength (output_rows)) strings_size_pre )
).

Definition filter_by_substring_partial_solve_wit_1 := 
forall (substring_pre: Z) (strings_size_pre: Z) (strings_pre: Z) (substring_l: (@list Z)) (rows: (@list (@list Z))) (PreH1 : (0 <= strings_size_pre)) (PreH2 : (strings_size_pre <= 100)) (PreH3 : (rows_well_formed_7 rows strings_size_pre )) (PreH4 : (valid_string substring_l )) (PreH5 : ((string_length (substring_l)) < INT_MAX)) (PreH6 : (problem_7_pre_z rows )) ,
  (CharPtrArray2.full strings_pre strings_size_pre rows )
  **  (store_string substring_pre substring_l )
|--
  “ (0 <= ((string_length (substring_l)) + 1 )) ” 
  &&  “ (0 <= strings_size_pre) ” 
  &&  “ (strings_size_pre <= 100) ” 
  &&  “ (rows_well_formed_7 rows strings_size_pre ) ” 
  &&  “ (valid_string substring_l ) ” 
  &&  “ ((string_length (substring_l)) < INT_MAX) ” 
  &&  “ (problem_7_pre_z rows ) ”
  &&  (CharArray.full substring_pre ((string_length (substring_l)) + 1 ) (c_string (substring_l)) )
  **  (CharPtrArray2.full strings_pre strings_size_pre rows )
.

Definition filter_by_substring_partial_solve_wit_2_pure := 
forall (substring_pre: Z) (strings_size_pre: Z) (strings_pre: Z) (substring_l: (@list Z)) (rows: (@list (@list Z))) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (substring_l)) + 1 ))) (PreH3 : (0 <= strings_size_pre)) (PreH4 : (strings_size_pre <= 100)) (PreH5 : (rows_well_formed_7 rows strings_size_pre )) (PreH6 : (valid_string substring_l )) (PreH7 : ((string_length (substring_l)) < INT_MAX)) (PreH8 : (problem_7_pre_z rows )) ,
  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full substring_pre ((string_length (substring_l)) + 1 ) (c_string (substring_l)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "substring" ) )) # Ptr  |-> substring_pre)
  **  ((( &( "strings_size" ) )) # Int  |-> strings_size_pre)
  **  ((( &( "strings" ) )) # Ptr  |-> strings_pre)
  **  (CharPtrArray2.full strings_pre strings_size_pre rows )
|--
  “ (0 <= strings_size_pre) ” 
  &&  “ (strings_size_pre < INT_MAX) ”
.

Definition filter_by_substring_partial_solve_wit_2_aux := 
forall (substring_pre: Z) (strings_size_pre: Z) (strings_pre: Z) (substring_l: (@list Z)) (rows: (@list (@list Z))) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (substring_l)) + 1 ))) (PreH3 : (0 <= strings_size_pre)) (PreH4 : (strings_size_pre <= 100)) (PreH5 : (rows_well_formed_7 rows strings_size_pre )) (PreH6 : (valid_string substring_l )) (PreH7 : ((string_length (substring_l)) < INT_MAX)) (PreH8 : (problem_7_pre_z rows )) ,
  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full substring_pre ((string_length (substring_l)) + 1 ) (c_string (substring_l)) )
  **  (CharPtrArray2.full strings_pre strings_size_pre rows )
|--
  “ (0 <= strings_size_pre) ” 
  &&  “ (strings_size_pre < INT_MAX) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= ((string_length (substring_l)) + 1 )) ” 
  &&  “ (0 <= strings_size_pre) ” 
  &&  “ (strings_size_pre <= 100) ” 
  &&  “ (rows_well_formed_7 rows strings_size_pre ) ” 
  &&  “ (valid_string substring_l ) ” 
  &&  “ ((string_length (substring_l)) < INT_MAX) ” 
  &&  “ (problem_7_pre_z rows ) ”
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full substring_pre ((string_length (substring_l)) + 1 ) (c_string (substring_l)) )
  **  (CharPtrArray2.full strings_pre strings_size_pre rows )
.

Definition filter_by_substring_partial_solve_wit_2 := filter_by_substring_partial_solve_wit_2_pure -> filter_by_substring_partial_solve_wit_2_aux.

Definition filter_by_substring_partial_solve_wit_3_pure := 
forall (substring_pre: Z) (strings_size_pre: Z) (strings_pre: Z) (substring_l: (@list Z)) (rows: (@list (@list Z))) (row_ptr: Z) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (i: Z) (output_size: Z) (out: Z) (data: Z) (hit: Z) (PreH1 : (0 <= i)) (PreH2 : (i < strings_size_pre)) (PreH3 : (0 <= output_size)) (PreH4 : (output_size <= i)) (PreH5 : (output_size = (Zlength (output_rows)))) (PreH6 : (output_size = (Zlength (output_ptrs)))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (rows_well_formed_7 rows strings_size_pre )) (PreH10 : (valid_string substring_l )) (PreH11 : ((string_length (substring_l)) < INT_MAX)) (PreH12 : (problem_7_pre_z rows )) (PreH13 : (filter_substring_state_7 rows substring_l i output_rows )) (PreH14 : (valid_string (row_payload_z_7 ((Znth (i) (rows) ((@nil Z))))) )) (PreH15 : ((string_length ((row_payload_z_7 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "strings_size" ) )) # Int  |-> strings_size_pre)
  **  ((( &( "strings" ) )) # Ptr  |-> strings_pre)
  **  ((( &( "substring" ) )) # Ptr  |-> substring_pre)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "hit" ) )) # Ptr  |-> hit)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.missing_i strings_pre strings_size_pre i row_ptr rows )
  **  (((strings_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_7 ((Znth (i) (rows) ((@nil Z))))) )
  **  (store_string substring_pre substring_l )
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size strings_size_pre )
|--
  “ (valid_string (row_payload_z_7 ((Znth (i) (rows) ((@nil Z))))) ) ” 
  &&  “ (valid_string substring_l ) ” 
  &&  “ ((string_length ((row_payload_z_7 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX) ” 
  &&  “ ((string_length (substring_l)) < INT_MAX) ”
.

Definition filter_by_substring_partial_solve_wit_3_aux := 
forall (substring_pre: Z) (strings_size_pre: Z) (strings_pre: Z) (substring_l: (@list Z)) (rows: (@list (@list Z))) (row_ptr: Z) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (i: Z) (output_size: Z) (out: Z) (data: Z) (PreH1 : (0 <= i)) (PreH2 : (i < strings_size_pre)) (PreH3 : (0 <= output_size)) (PreH4 : (output_size <= i)) (PreH5 : (output_size = (Zlength (output_rows)))) (PreH6 : (output_size = (Zlength (output_ptrs)))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (rows_well_formed_7 rows strings_size_pre )) (PreH10 : (valid_string substring_l )) (PreH11 : ((string_length (substring_l)) < INT_MAX)) (PreH12 : (problem_7_pre_z rows )) (PreH13 : (filter_substring_state_7 rows substring_l i output_rows )) (PreH14 : (valid_string (row_payload_z_7 ((Znth (i) (rows) ((@nil Z))))) )) (PreH15 : ((string_length ((row_payload_z_7 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX)) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.missing_i strings_pre strings_size_pre i row_ptr rows )
  **  (((strings_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_7 ((Znth (i) (rows) ((@nil Z))))) )
  **  (store_string substring_pre substring_l )
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size strings_size_pre )
|--
  “ (valid_string (row_payload_z_7 ((Znth (i) (rows) ((@nil Z))))) ) ” 
  &&  “ (valid_string substring_l ) ” 
  &&  “ ((string_length ((row_payload_z_7 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX) ” 
  &&  “ ((string_length (substring_l)) < INT_MAX) ” 
  &&  “ (0 <= ((string_length (substring_l)) + 1 )) ” 
  &&  “ (0 <= ((string_length ((row_payload_z_7 ((Znth (i) (rows) ((@nil Z))))))) + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < strings_size_pre) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= i) ” 
  &&  “ (output_size = (Zlength (output_rows))) ” 
  &&  “ (output_size = (Zlength (output_ptrs))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (rows_well_formed_7 rows strings_size_pre ) ” 
  &&  “ (valid_string substring_l ) ” 
  &&  “ ((string_length (substring_l)) < INT_MAX) ” 
  &&  “ (problem_7_pre_z rows ) ” 
  &&  “ (filter_substring_state_7 rows substring_l i output_rows ) ” 
  &&  “ (valid_string (row_payload_z_7 ((Znth (i) (rows) ((@nil Z))))) ) ” 
  &&  “ ((string_length ((row_payload_z_7 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX) ”
  &&  (store_string row_ptr (row_payload_z_7 ((Znth (i) (rows) ((@nil Z))))) )
  **  (store_string substring_pre substring_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.missing_i strings_pre strings_size_pre i row_ptr rows )
  **  (((strings_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size strings_size_pre )
.

Definition filter_by_substring_partial_solve_wit_3 := filter_by_substring_partial_solve_wit_3_pure -> filter_by_substring_partial_solve_wit_3_aux.

Definition filter_by_substring_partial_solve_wit_4 := 
forall (substring_pre: Z) (strings_size_pre: Z) (strings_pre: Z) (substring_l: (@list Z)) (rows: (@list (@list Z))) (row_ptr: Z) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (i: Z) (output_size: Z) (hit: Z) (out: Z) (data: Z) (PreH1 : (0 <= i)) (PreH2 : (i < strings_size_pre)) (PreH3 : (0 <= output_size)) (PreH4 : (output_size <= i)) (PreH5 : (output_size = (Zlength (output_rows)))) (PreH6 : (output_size = (Zlength (output_ptrs)))) (PreH7 : (hit <> 0)) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (rows_well_formed_7 rows strings_size_pre )) (PreH11 : (valid_string substring_l )) (PreH12 : ((string_length (substring_l)) < INT_MAX)) (PreH13 : (problem_7_pre_z rows )) (PreH14 : (filter_substring_state_7 rows substring_l i output_rows )) (PreH15 : (substring_match_z_7 (Znth (i) (rows) ((@nil Z))) substring_l )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.missing_i strings_pre strings_size_pre i row_ptr rows )
  **  (((strings_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
  **  (store_string substring_pre substring_l )
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size strings_size_pre )
|--
  “ (0 <= ((string_length (substring_l)) + 1 )) ” 
  &&  “ (0 <= (Zlength ((Znth (i) (rows) ((@nil Z)))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < strings_size_pre) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= i) ” 
  &&  “ (output_size = (Zlength (output_rows))) ” 
  &&  “ (output_size = (Zlength (output_ptrs))) ” 
  &&  “ (hit <> 0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (rows_well_formed_7 rows strings_size_pre ) ” 
  &&  “ (valid_string substring_l ) ” 
  &&  “ ((string_length (substring_l)) < INT_MAX) ” 
  &&  “ (problem_7_pre_z rows ) ” 
  &&  “ (filter_substring_state_7 rows substring_l i output_rows ) ” 
  &&  “ (substring_match_z_7 (Znth (i) (rows) ((@nil Z))) substring_l ) ”
  &&  (((data + (output_size * sizeof(PTR) ) )) # Ptr  |->_)
  **  (PtrArray.undef_seg data (output_size + 1 ) strings_size_pre )
  **  (CharArray.full substring_pre ((string_length (substring_l)) + 1 ) (c_string (substring_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.missing_i strings_pre strings_size_pre i row_ptr rows )
  **  (((strings_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
  **  (PtrArray.seg data 0 output_size output_ptrs )
.

Module Type VC_Correct.

Include ptr_array2_Strategy_Correct.
Include char_array_Strategy_Correct.
Include string_Strategy_Correct.

Axiom proof_of_filter_by_substring_safety_wit_1 : filter_by_substring_safety_wit_1.
Axiom proof_of_filter_by_substring_safety_wit_2 : filter_by_substring_safety_wit_2.
Axiom proof_of_filter_by_substring_safety_wit_3 : filter_by_substring_safety_wit_3.
Axiom proof_of_filter_by_substring_safety_wit_4 : filter_by_substring_safety_wit_4.
Axiom proof_of_filter_by_substring_safety_wit_5 : filter_by_substring_safety_wit_5.
Axiom proof_of_filter_by_substring_safety_wit_6 : filter_by_substring_safety_wit_6.
Axiom proof_of_filter_by_substring_safety_wit_7 : filter_by_substring_safety_wit_7.
Axiom proof_of_filter_by_substring_safety_wit_8 : filter_by_substring_safety_wit_8.
Axiom proof_of_filter_by_substring_safety_wit_9 : filter_by_substring_safety_wit_9.
Axiom proof_of_filter_by_substring_safety_wit_10 : filter_by_substring_safety_wit_10.
Axiom proof_of_filter_by_substring_entail_wit_1 : filter_by_substring_entail_wit_1.
Axiom proof_of_filter_by_substring_entail_wit_2 : filter_by_substring_entail_wit_2.
Axiom proof_of_filter_by_substring_entail_wit_3 : filter_by_substring_entail_wit_3.
Axiom proof_of_filter_by_substring_entail_wit_4 : filter_by_substring_entail_wit_4.
Axiom proof_of_filter_by_substring_entail_wit_5 : filter_by_substring_entail_wit_5.
Axiom proof_of_filter_by_substring_entail_wit_6 : filter_by_substring_entail_wit_6.
Axiom proof_of_filter_by_substring_entail_wit_7 : filter_by_substring_entail_wit_7.
Axiom proof_of_filter_by_substring_entail_wit_8_1 : filter_by_substring_entail_wit_8_1.
Axiom proof_of_filter_by_substring_entail_wit_8_2 : filter_by_substring_entail_wit_8_2.
Axiom proof_of_filter_by_substring_return_wit_1 : filter_by_substring_return_wit_1.
Axiom proof_of_filter_by_substring_partial_solve_wit_1 : filter_by_substring_partial_solve_wit_1.
Axiom proof_of_filter_by_substring_partial_solve_wit_2_pure : filter_by_substring_partial_solve_wit_2_pure.
Axiom proof_of_filter_by_substring_partial_solve_wit_2 : filter_by_substring_partial_solve_wit_2.
Axiom proof_of_filter_by_substring_partial_solve_wit_3_pure : filter_by_substring_partial_solve_wit_3_pure.
Axiom proof_of_filter_by_substring_partial_solve_wit_3 : filter_by_substring_partial_solve_wit_3.
Axiom proof_of_filter_by_substring_partial_solve_wit_4 : filter_by_substring_partial_solve_wit_4.

End VC_Correct.
