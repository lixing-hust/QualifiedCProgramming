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
Require Import SimpleC.EE.coins_29.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import ptr_array2_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import ptr_array2_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_proof.
From SimpleC.StdLib Require Import string_strategy_goal.
From SimpleC.StdLib Require Import string_strategy_proof.

(*----- Function filter_by_prefix -----*)

Definition filter_by_prefix_safety_wit_1 := 
forall (prefix_pre: Z) (strings_size_pre: Z) (strings_pre: Z) (prefix_addr: Z) (strings_addr: Z) (prefix_l: (@list Z)) (rows: (@list (@list Z))) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (prefix_l)) + 1 ))) (PreH3 : (strings_pre = strings_addr)) (PreH4 : (prefix_pre = prefix_addr)) (PreH5 : (0 <= strings_size_pre)) (PreH6 : (strings_size_pre < INT_MAX)) (PreH7 : (rows_well_formed_29 rows strings_size_pre )) (PreH8 : (problem_29_pre_z rows )) (PreH9 : (valid_string prefix_l )) (PreH10 : ((string_length (prefix_l)) < INT_MAX)) ,
  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (CharArray.full prefix_pre ((string_length (prefix_l)) + 1 ) (c_string (prefix_l)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "strings_size" ) )) # Int  |-> strings_size_pre)
  **  ((( &( "strings" ) )) # Ptr  |-> strings_pre)
  **  (CharPtrArray2.full strings_pre strings_size_pre rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition filter_by_prefix_safety_wit_2 := 
forall (prefix_pre: Z) (strings_size_pre: Z) (strings_pre: Z) (prefix_addr: Z) (strings_addr: Z) (prefix_l: (@list Z)) (rows: (@list (@list Z))) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= ((string_length (prefix_l)) + 1 ))) (PreH4 : (strings_pre = strings_addr)) (PreH5 : (prefix_pre = prefix_addr)) (PreH6 : (0 <= strings_size_pre)) (PreH7 : (strings_size_pre < INT_MAX)) (PreH8 : (rows_well_formed_29 rows strings_size_pre )) (PreH9 : (problem_29_pre_z rows )) (PreH10 : (valid_string prefix_l )) (PreH11 : ((string_length (prefix_l)) < INT_MAX)) ,
  ((( &( "output_size" ) )) # Int  |->_)
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (PtrArray.undef_seg retval_2 0 strings_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full prefix_pre ((string_length (prefix_l)) + 1 ) (c_string (prefix_l)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "strings_size" ) )) # Int  |-> strings_size_pre)
  **  ((( &( "strings" ) )) # Ptr  |-> strings_pre)
  **  (CharPtrArray2.full strings_pre strings_size_pre rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition filter_by_prefix_safety_wit_3 := 
forall (prefix_pre: Z) (strings_size_pre: Z) (strings_pre: Z) (prefix_addr: Z) (strings_addr: Z) (prefix_l: (@list Z)) (rows: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = (string_length (prefix_l)))) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (0 <= ((string_length (prefix_l)) + 1 ))) (PreH5 : (strings_pre = strings_addr)) (PreH6 : (prefix_pre = prefix_addr)) (PreH7 : (0 <= strings_size_pre)) (PreH8 : (strings_size_pre < INT_MAX)) (PreH9 : (rows_well_formed_29 rows strings_size_pre )) (PreH10 : (problem_29_pre_z rows )) (PreH11 : (valid_string prefix_l )) (PreH12 : ((string_length (prefix_l)) < INT_MAX)) ,
  ((( &( "cur" ) )) # Ptr  |->_)
  **  (store_string prefix_pre prefix_l )
  **  ((( &( "plen" ) )) # Int  |-> retval_3)
  **  ((( &( "output_size" ) )) # Int  |-> 0)
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (PtrArray.undef_seg retval_2 0 strings_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "strings_size" ) )) # Int  |-> strings_size_pre)
  **  ((( &( "strings" ) )) # Ptr  |-> strings_pre)
  **  (CharPtrArray2.full strings_pre strings_size_pre rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition filter_by_prefix_safety_wit_4 := 
forall (prefix_pre: Z) (strings_size_pre: Z) (strings_pre: Z) (prefix_addr: Z) (strings_addr: Z) (prefix_l: (@list Z)) (rows: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = (string_length (prefix_l)))) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (0 <= ((string_length (prefix_l)) + 1 ))) (PreH5 : (strings_pre = strings_addr)) (PreH6 : (prefix_pre = prefix_addr)) (PreH7 : (0 <= strings_size_pre)) (PreH8 : (strings_size_pre < INT_MAX)) (PreH9 : (rows_well_formed_29 rows strings_size_pre )) (PreH10 : (problem_29_pre_z rows )) (PreH11 : (valid_string prefix_l )) (PreH12 : ((string_length (prefix_l)) < INT_MAX)) ,
  ((( &( "cmp" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Ptr  |-> 0)
  **  (store_string prefix_pre prefix_l )
  **  ((( &( "plen" ) )) # Int  |-> retval_3)
  **  ((( &( "output_size" ) )) # Int  |-> 0)
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (PtrArray.undef_seg retval_2 0 strings_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "strings_size" ) )) # Int  |-> strings_size_pre)
  **  ((( &( "strings" ) )) # Ptr  |-> strings_pre)
  **  (CharPtrArray2.full strings_pre strings_size_pre rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition filter_by_prefix_safety_wit_5 := 
forall (prefix_pre: Z) (strings_size_pre: Z) (strings_pre: Z) (prefix_addr: Z) (strings_addr: Z) (prefix_l: (@list Z)) (rows: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = (string_length (prefix_l)))) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (0 <= ((string_length (prefix_l)) + 1 ))) (PreH5 : (strings_pre = strings_addr)) (PreH6 : (prefix_pre = prefix_addr)) (PreH7 : (0 <= strings_size_pre)) (PreH8 : (strings_size_pre < INT_MAX)) (PreH9 : (rows_well_formed_29 rows strings_size_pre )) (PreH10 : (problem_29_pre_z rows )) (PreH11 : (valid_string prefix_l )) (PreH12 : ((string_length (prefix_l)) < INT_MAX)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "cmp" ) )) # Int  |-> 0)
  **  ((( &( "cur" ) )) # Ptr  |-> 0)
  **  (store_string prefix_pre prefix_l )
  **  ((( &( "plen" ) )) # Int  |-> retval_3)
  **  ((( &( "output_size" ) )) # Int  |-> 0)
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (PtrArray.undef_seg retval_2 0 strings_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "strings_size" ) )) # Int  |-> strings_size_pre)
  **  ((( &( "strings" ) )) # Ptr  |-> strings_pre)
  **  (CharPtrArray2.full strings_pre strings_size_pre rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition filter_by_prefix_safety_wit_6 := 
forall (strings_size_pre: Z) (prefix_addr: Z) (strings_addr: Z) (prefix_l: (@list Z)) (rows: (@list (@list Z))) (row_ptr: Z) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (i: Z) (output_size: Z) (plen: Z) (out: Z) (data: Z) (retval: Z) (PreH1 : (strncmp_result (row_payload_z_29 ((Znth (i) (rows) ((@nil Z))))) prefix_l plen retval )) (PreH2 : (0 <= ((string_length (prefix_l)) + 1 ))) (PreH3 : (0 <= ((string_length ((row_payload_z_29 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) (PreH4 : (0 <= i)) (PreH5 : (i < strings_size_pre)) (PreH6 : (0 <= output_size)) (PreH7 : (output_size <= i)) (PreH8 : (output_size = (Zlength (output_rows)))) (PreH9 : (output_size = (Zlength (output_ptrs)))) (PreH10 : (plen = (string_length (prefix_l)))) (PreH11 : (out <> 0)) (PreH12 : (data <> 0)) (PreH13 : (rows_well_formed_29 rows strings_size_pre )) (PreH14 : (row_well_formed_29 (Znth (i) (rows) ((@nil Z))) )) (PreH15 : (problem_29_pre_z rows )) (PreH16 : (valid_string prefix_l )) (PreH17 : ((string_length (prefix_l)) < INT_MAX)) (PreH18 : (filter_prefix_state_29 rows prefix_l i output_rows )) ,
  (store_string row_ptr (row_payload_z_29 ((Znth (i) (rows) ((@nil Z))))) )
  **  (store_string prefix_addr prefix_l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "strings" ) )) # Ptr  |-> strings_addr)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_addr)
  **  ((( &( "strings_size" ) )) # Int  |-> strings_size_pre)
  **  ((( &( "plen" ) )) # Int  |-> plen)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "cmp" ) )) # Int  |-> retval)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.missing_i strings_addr strings_size_pre i row_ptr rows )
  **  (((strings_addr + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size strings_size_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition filter_by_prefix_safety_wit_7 := 
forall (strings_size_pre: Z) (prefix_addr: Z) (strings_addr: Z) (prefix_l: (@list Z)) (rows: (@list (@list Z))) (row_ptr: Z) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (i: Z) (output_size: Z) (plen: Z) (out: Z) (data: Z) (cmp: Z) (PreH1 : (0 <= ((string_length (prefix_l)) + 1 ))) (PreH2 : (0 <= ((string_length ((row_payload_z_29 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < strings_size_pre)) (PreH5 : (0 <= output_size)) (PreH6 : (output_size <= i)) (PreH7 : (output_size = (Zlength (output_rows)))) (PreH8 : (output_size = (Zlength (output_ptrs)))) (PreH9 : (plen = (string_length (prefix_l)))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (cmp = 0)) (PreH13 : (rows_well_formed_29 rows strings_size_pre )) (PreH14 : (problem_29_pre_z rows )) (PreH15 : (valid_string prefix_l )) (PreH16 : ((string_length (prefix_l)) < INT_MAX)) (PreH17 : (row_well_formed_29 (Znth (i) (rows) ((@nil Z))) )) (PreH18 : (prefix_hit_z_29 (row_payload_z_29 ((Znth (i) (rows) ((@nil Z))))) prefix_l )) (PreH19 : (filter_prefix_state_29 rows prefix_l i output_rows )) ,
  (PtrArray.seg data 0 (output_size + 1 ) (app (output_ptrs) ((cons (row_ptr) ((@nil Z))))) )
  **  (PtrArray.undef_seg data (output_size + 1 ) strings_size_pre )
  **  (CharArray.full prefix_addr ((string_length (prefix_l)) + 1 ) (c_string (prefix_l)) )
  **  (CharArray.full row_ptr ((string_length ((row_payload_z_29 ((Znth (i) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_29 ((Znth (i) (rows) ((@nil Z))))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "strings" ) )) # Ptr  |-> strings_addr)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_addr)
  **  ((( &( "strings_size" ) )) # Int  |-> strings_size_pre)
  **  ((( &( "plen" ) )) # Int  |-> plen)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.missing_i strings_addr strings_size_pre i row_ptr rows )
  **  (((strings_addr + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ ((output_size + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (output_size + 1 )) ”
.

Definition filter_by_prefix_safety_wit_8 := 
forall (strings_size_pre: Z) (prefix_addr: Z) (strings_addr: Z) (prefix_l: (@list Z)) (rows: (@list (@list Z))) (row_ptr: Z) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (i: Z) (output_size: Z) (plen: Z) (out: Z) (data: Z) (cmp: Z) (PreH1 : (0 <= ((string_length (prefix_l)) + 1 ))) (PreH2 : (0 <= ((string_length ((row_payload_z_29 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < strings_size_pre)) (PreH5 : (0 <= output_size)) (PreH6 : (output_size <= i)) (PreH7 : (output_size = (Zlength (output_rows)))) (PreH8 : (output_size = (Zlength (output_ptrs)))) (PreH9 : (plen = (string_length (prefix_l)))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (cmp = 0)) (PreH13 : (rows_well_formed_29 rows strings_size_pre )) (PreH14 : (problem_29_pre_z rows )) (PreH15 : (valid_string prefix_l )) (PreH16 : ((string_length (prefix_l)) < INT_MAX)) (PreH17 : (row_well_formed_29 (Znth (i) (rows) ((@nil Z))) )) (PreH18 : (prefix_hit_z_29 (row_payload_z_29 ((Znth (i) (rows) ((@nil Z))))) prefix_l )) (PreH19 : (filter_prefix_state_29 rows prefix_l i output_rows )) ,
  (PtrArray.seg data 0 (output_size + 1 ) (app (output_ptrs) ((cons (row_ptr) ((@nil Z))))) )
  **  (PtrArray.undef_seg data (output_size + 1 ) strings_size_pre )
  **  (CharArray.full prefix_addr ((string_length (prefix_l)) + 1 ) (c_string (prefix_l)) )
  **  (CharArray.full row_ptr ((string_length ((row_payload_z_29 ((Znth (i) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_29 ((Znth (i) (rows) ((@nil Z))))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "strings" ) )) # Ptr  |-> strings_addr)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_addr)
  **  ((( &( "strings_size" ) )) # Int  |-> strings_size_pre)
  **  ((( &( "plen" ) )) # Int  |-> plen)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.missing_i strings_addr strings_size_pre i row_ptr rows )
  **  (((strings_addr + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition filter_by_prefix_safety_wit_9 := 
forall (strings_size_pre: Z) (prefix_addr: Z) (strings_addr: Z) (prefix_l: (@list Z)) (rows: (@list (@list Z))) (row_ptr: Z) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (i: Z) (output_size: Z) (plen: Z) (out: Z) (data: Z) (cmp: Z) (PreH1 : (0 <= ((string_length (prefix_l)) + 1 ))) (PreH2 : (0 <= ((string_length ((row_payload_z_29 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < strings_size_pre)) (PreH5 : (0 <= output_size)) (PreH6 : (output_size <= i)) (PreH7 : (output_size = (Zlength (output_rows)))) (PreH8 : (output_size = (Zlength (output_ptrs)))) (PreH9 : (plen = (string_length (prefix_l)))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (cmp = 0)) (PreH13 : (rows_well_formed_29 rows strings_size_pre )) (PreH14 : (problem_29_pre_z rows )) (PreH15 : (valid_string prefix_l )) (PreH16 : ((string_length (prefix_l)) < INT_MAX)) (PreH17 : (row_well_formed_29 (Znth (i) (rows) ((@nil Z))) )) (PreH18 : (prefix_hit_z_29 (row_payload_z_29 ((Znth (i) (rows) ((@nil Z))))) prefix_l )) (PreH19 : (filter_prefix_state_29 rows prefix_l i output_rows )) ,
  (PtrArray.seg data 0 (output_size + 1 ) (app (output_ptrs) ((cons (row_ptr) ((@nil Z))))) )
  **  (PtrArray.undef_seg data (output_size + 1 ) strings_size_pre )
  **  (CharArray.full prefix_addr ((string_length (prefix_l)) + 1 ) (c_string (prefix_l)) )
  **  (CharArray.full row_ptr ((string_length ((row_payload_z_29 ((Znth (i) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_29 ((Znth (i) (rows) ((@nil Z))))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "output_size" ) )) # Int  |-> (output_size + 1 ))
  **  ((( &( "strings" ) )) # Ptr  |-> strings_addr)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_addr)
  **  ((( &( "strings_size" ) )) # Int  |-> strings_size_pre)
  **  ((( &( "plen" ) )) # Int  |-> plen)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.missing_i strings_addr strings_size_pre i row_ptr rows )
  **  (((strings_addr + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition filter_by_prefix_safety_wit_10 := 
forall (strings_size_pre: Z) (prefix_addr: Z) (strings_addr: Z) (prefix_l: (@list Z)) (rows: (@list (@list Z))) (row_ptr: Z) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (i: Z) (output_size: Z) (plen: Z) (out: Z) (data: Z) (cmp: Z) (PreH1 : (0 <= i)) (PreH2 : (i < strings_size_pre)) (PreH3 : (0 <= output_size)) (PreH4 : (output_size <= i)) (PreH5 : (output_size = (Zlength (output_rows)))) (PreH6 : (output_size = (Zlength (output_ptrs)))) (PreH7 : (plen = (string_length (prefix_l)))) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (cmp <> 0)) (PreH11 : (rows_well_formed_29 rows strings_size_pre )) (PreH12 : (problem_29_pre_z rows )) (PreH13 : (valid_string prefix_l )) (PreH14 : ((string_length (prefix_l)) < INT_MAX)) (PreH15 : (row_well_formed_29 (Znth (i) (rows) ((@nil Z))) )) (PreH16 : (prefix_miss_z_29 (row_payload_z_29 ((Znth (i) (rows) ((@nil Z))))) prefix_l )) (PreH17 : (filter_prefix_state_29 rows prefix_l i output_rows )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "strings" ) )) # Ptr  |-> strings_addr)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_addr)
  **  ((( &( "strings_size" ) )) # Int  |-> strings_size_pre)
  **  ((( &( "plen" ) )) # Int  |-> plen)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.missing_i strings_addr strings_size_pre i row_ptr rows )
  **  (((strings_addr + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_29 ((Znth (i) (rows) ((@nil Z))))) )
  **  (store_string prefix_addr prefix_l )
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size strings_size_pre )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition filter_by_prefix_entail_wit_1 := 
(
forall (prefix_pre: Z) (strings_size_pre: Z) (strings_pre: Z) (prefix_addr: Z) (strings_addr: Z) (prefix_l: (@list Z)) (rows: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = (string_length (prefix_l)))) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (0 <= ((string_length (prefix_l)) + 1 ))) (PreH5 : (strings_pre = strings_addr)) (PreH6 : (prefix_pre = prefix_addr)) (PreH7 : (0 <= strings_size_pre)) (PreH8 : (strings_size_pre < INT_MAX)) (PreH9 : (rows_well_formed_29 rows strings_size_pre )) (PreH10 : (problem_29_pre_z rows )) (PreH11 : (valid_string prefix_l )) (PreH12 : ((string_length (prefix_l)) < INT_MAX)) ,
  (store_string prefix_pre prefix_l )
  **  (PtrArray.undef_seg retval_2 0 strings_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "strings" ) )) # Ptr  |-> strings_pre)
  **  (CharPtrArray2.full strings_pre strings_size_pre rows )
|--
  EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= strings_size_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 = (Zlength (output_rows))) ” 
  &&  “ (0 = (Zlength (output_ptrs))) ” 
  &&  “ (retval_3 = (string_length (prefix_l))) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (rows_well_formed_29 rows strings_size_pre ) ” 
  &&  “ (problem_29_pre_z rows ) ” 
  &&  “ (valid_string prefix_l ) ” 
  &&  “ ((string_length (prefix_l)) < INT_MAX) ” 
  &&  “ (filter_prefix_state_29 rows prefix_l 0 output_rows ) ”
  &&  ((( &( "strings" ) )) # Ptr  |-> strings_addr)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_addr)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.full strings_addr strings_size_pre rows )
  **  (store_string prefix_addr prefix_l )
  **  (PtrArray.seg retval_2 0 0 output_ptrs )
  **  (PtrArray.undef_seg retval_2 0 strings_size_pre )
) \/
(
forall (prefix_pre: Z) (strings_size_pre: Z) (strings_pre: Z) (prefix_addr: Z) (strings_addr: Z) (prefix_l: (@list Z)) (rows: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = (string_length (prefix_l)))) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (0 <= ((string_length (prefix_l)) + 1 ))) (PreH5 : (strings_pre = strings_addr)) (PreH6 : (prefix_pre = prefix_addr)) (PreH7 : (0 <= strings_size_pre)) (PreH8 : (strings_size_pre < INT_MAX)) (PreH9 : (rows_well_formed_29 rows strings_size_pre )) (PreH10 : (problem_29_pre_z rows )) (PreH11 : (valid_string prefix_l )) (PreH12 : ((string_length (prefix_l)) < INT_MAX)) ,
  (CharArray.full prefix_pre ((string_length (prefix_l)) + 1 ) (c_string (prefix_l)) )
  **  (CharPtrArray2.full strings_pre strings_size_pre rows )
|--
  EX (output_rows: (@list (@list Z))) ,
  “ (strings_pre = strings_addr) ” 
  &&  “ (prefix_pre = prefix_addr) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= strings_size_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 = (Zlength (output_rows))) ” 
  &&  “ (0 = (Zlength ((@nil Z)))) ” 
  &&  “ (retval_3 = (string_length (prefix_l))) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (rows_well_formed_29 rows strings_size_pre ) ” 
  &&  “ (problem_29_pre_z rows ) ” 
  &&  “ (valid_string prefix_l ) ” 
  &&  “ ((string_length (prefix_l)) < INT_MAX) ” 
  &&  “ (filter_prefix_state_29 rows prefix_l 0 output_rows ) ”
  &&  (CharArray.full prefix_addr ((string_length (prefix_l)) + 1 ) (c_string (prefix_l)) )
  **  (CharPtrArray2.full strings_addr strings_size_pre rows )
).

Definition filter_by_prefix_entail_wit_2 := 
(
forall (strings_size_pre: Z) (prefix_addr: Z) (strings_addr: Z) (prefix_l: (@list Z)) (rows: (@list (@list Z))) (data: Z) (out: Z) (plen: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (output_size: Z) (i: Z) (PreH1 : (i < strings_size_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= strings_size_pre)) (PreH4 : (0 <= output_size)) (PreH5 : (output_size <= i)) (PreH6 : (output_size = (Zlength (output_rows_2)))) (PreH7 : (output_size = (Zlength (output_ptrs_2)))) (PreH8 : (plen = (string_length (prefix_l)))) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (rows_well_formed_29 rows strings_size_pre )) (PreH12 : (problem_29_pre_z rows )) (PreH13 : (valid_string prefix_l )) (PreH14 : ((string_length (prefix_l)) < INT_MAX)) (PreH15 : (filter_prefix_state_29 rows prefix_l i output_rows_2 )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.full strings_addr strings_size_pre rows )
  **  (store_string prefix_addr prefix_l )
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
  &&  “ (plen = (string_length (prefix_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (rows_well_formed_29 rows strings_size_pre ) ” 
  &&  “ (row_well_formed_29 (Znth (i) (rows) ((@nil Z))) ) ” 
  &&  “ (problem_29_pre_z rows ) ” 
  &&  “ (valid_string prefix_l ) ” 
  &&  “ ((string_length (prefix_l)) < INT_MAX) ” 
  &&  “ (filter_prefix_state_29 rows prefix_l i output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.missing_i strings_addr strings_size_pre i row_ptr rows )
  **  (((strings_addr + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_29 ((Znth (i) (rows) ((@nil Z))))) )
  **  (store_string prefix_addr prefix_l )
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size strings_size_pre )
) \/
(
forall (strings_size_pre: Z) (prefix_l: (@list Z)) (rows: (@list (@list Z))) (data: Z) (out: Z) (plen: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (output_size: Z) (i: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (0 <= ((string_length (prefix_l)) + 1 ))) (PreH2 : (0 <= (Zlength ((Znth i rows __default__List_Z))))) (PreH3 : (i < strings_size_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= strings_size_pre)) (PreH6 : (0 <= output_size)) (PreH7 : (output_size <= i)) (PreH8 : (output_size = (Zlength (output_rows_2)))) (PreH9 : (output_size = (Zlength (output_ptrs_2)))) (PreH10 : (plen = (string_length (prefix_l)))) (PreH11 : (out <> 0)) (PreH12 : (data <> 0)) (PreH13 : (rows_well_formed_29 rows strings_size_pre )) (PreH14 : (problem_29_pre_z rows )) (PreH15 : (valid_string prefix_l )) (PreH16 : ((string_length (prefix_l)) < INT_MAX)) (PreH17 : (filter_prefix_state_29 rows prefix_l i output_rows_2 )) ,
  (CharArray.full row_ptr_2 (Zlength ((Znth i rows __default__List_Z))) (Znth i rows __default__List_Z) )
|--
  EX (output_rows: (@list (@list Z))) ,
  “ (0 <= i) ” 
  &&  “ (i < strings_size_pre) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= i) ” 
  &&  “ (output_size = (Zlength (output_rows))) ” 
  &&  “ (output_size = (Zlength (output_ptrs_2))) ” 
  &&  “ (plen = (string_length (prefix_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (rows_well_formed_29 rows strings_size_pre ) ” 
  &&  “ (row_well_formed_29 (Znth (i) (rows) ((@nil Z))) ) ” 
  &&  “ (problem_29_pre_z rows ) ” 
  &&  “ (valid_string prefix_l ) ” 
  &&  “ ((string_length (prefix_l)) < INT_MAX) ” 
  &&  “ (filter_prefix_state_29 rows prefix_l i output_rows ) ”
  &&  (CharArray.full row_ptr_2 ((string_length ((row_payload_z_29 ((Znth (i) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_29 ((Znth (i) (rows) ((@nil Z))))))) )
).

Definition filter_by_prefix_entail_wit_3 := 
(
forall (strings_size_pre: Z) (prefix_addr: Z) (strings_addr: Z) (prefix_l: (@list Z)) (rows: (@list (@list Z))) (row_ptr: Z) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (i: Z) (output_size: Z) (plen: Z) (out: Z) (data: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (strncmp_result (row_payload_z_29 ((Znth (i) (rows) ((@nil Z))))) prefix_l plen retval )) (PreH3 : (0 <= ((string_length (prefix_l)) + 1 ))) (PreH4 : (0 <= ((string_length ((row_payload_z_29 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) (PreH5 : (0 <= i)) (PreH6 : (i < strings_size_pre)) (PreH7 : (0 <= output_size)) (PreH8 : (output_size <= i)) (PreH9 : (output_size = (Zlength (output_rows_2)))) (PreH10 : (output_size = (Zlength (output_ptrs_2)))) (PreH11 : (plen = (string_length (prefix_l)))) (PreH12 : (out <> 0)) (PreH13 : (data <> 0)) (PreH14 : (rows_well_formed_29 rows strings_size_pre )) (PreH15 : (row_well_formed_29 (Znth (i) (rows) ((@nil Z))) )) (PreH16 : (problem_29_pre_z rows )) (PreH17 : (valid_string prefix_l )) (PreH18 : ((string_length (prefix_l)) < INT_MAX)) (PreH19 : (filter_prefix_state_29 rows prefix_l i output_rows_2 )) ,
  (store_string row_ptr (row_payload_z_29 ((Znth (i) (rows) ((@nil Z))))) )
  **  (store_string prefix_addr prefix_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.missing_i strings_addr strings_size_pre i row_ptr rows )
  **  (((strings_addr + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
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
  &&  “ (plen = (string_length (prefix_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (rows_well_formed_29 rows strings_size_pre ) ” 
  &&  “ (problem_29_pre_z rows ) ” 
  &&  “ (valid_string prefix_l ) ” 
  &&  “ ((string_length (prefix_l)) < INT_MAX) ” 
  &&  “ (row_well_formed_29 (Znth (i) (rows) ((@nil Z))) ) ” 
  &&  “ (prefix_hit_z_29 (row_payload_z_29 ((Znth (i) (rows) ((@nil Z))))) prefix_l ) ” 
  &&  “ (filter_prefix_state_29 rows prefix_l i output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.missing_i strings_addr strings_size_pre i row_ptr rows )
  **  (((strings_addr + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_29 ((Znth (i) (rows) ((@nil Z))))) )
  **  (store_string prefix_addr prefix_l )
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size strings_size_pre )
) \/
(
forall (strings_size_pre: Z) (prefix_l: (@list Z)) (rows: (@list (@list Z))) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (i: Z) (output_size: Z) (plen: Z) (out: Z) (data: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (strncmp_result (row_payload_z_29 ((Znth (i) (rows) ((@nil Z))))) prefix_l plen retval )) (PreH3 : (0 <= ((string_length (prefix_l)) + 1 ))) (PreH4 : (0 <= ((string_length ((row_payload_z_29 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) (PreH5 : (0 <= i)) (PreH6 : (i < strings_size_pre)) (PreH7 : (0 <= output_size)) (PreH8 : (output_size <= i)) (PreH9 : (output_size = (Zlength (output_rows_2)))) (PreH10 : (output_size = (Zlength (output_ptrs_2)))) (PreH11 : (plen = (string_length (prefix_l)))) (PreH12 : (out <> 0)) (PreH13 : (data <> 0)) (PreH14 : (rows_well_formed_29 rows strings_size_pre )) (PreH15 : (row_well_formed_29 (Znth (i) (rows) ((@nil Z))) )) (PreH16 : (problem_29_pre_z rows )) (PreH17 : (valid_string prefix_l )) (PreH18 : ((string_length (prefix_l)) < INT_MAX)) (PreH19 : (filter_prefix_state_29 rows prefix_l i output_rows_2 )) ,
  TT && emp 
|--
  EX (output_rows: (@list (@list Z))) ,
  “ (0 <= i) ” 
  &&  “ (i < strings_size_pre) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= i) ” 
  &&  “ (output_size = (Zlength (output_rows))) ” 
  &&  “ (output_size = (Zlength (output_ptrs_2))) ” 
  &&  “ (plen = (string_length (prefix_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (rows_well_formed_29 rows strings_size_pre ) ” 
  &&  “ (problem_29_pre_z rows ) ” 
  &&  “ (valid_string prefix_l ) ” 
  &&  “ ((string_length (prefix_l)) < INT_MAX) ” 
  &&  “ (row_well_formed_29 (Znth (i) (rows) ((@nil Z))) ) ” 
  &&  “ (prefix_hit_z_29 (row_payload_z_29 ((Znth (i) (rows) ((@nil Z))))) prefix_l ) ” 
  &&  “ (filter_prefix_state_29 rows prefix_l i output_rows ) ”
  &&  emp
).

Definition filter_by_prefix_entail_wit_4 := 
(
forall (strings_size_pre: Z) (prefix_addr: Z) (strings_addr: Z) (prefix_l: (@list Z)) (rows: (@list (@list Z))) (row_ptr: Z) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (i: Z) (output_size: Z) (plen: Z) (out: Z) (data: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (strncmp_result (row_payload_z_29 ((Znth (i) (rows) ((@nil Z))))) prefix_l plen retval )) (PreH3 : (0 <= ((string_length (prefix_l)) + 1 ))) (PreH4 : (0 <= ((string_length ((row_payload_z_29 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) (PreH5 : (0 <= i)) (PreH6 : (i < strings_size_pre)) (PreH7 : (0 <= output_size)) (PreH8 : (output_size <= i)) (PreH9 : (output_size = (Zlength (output_rows_2)))) (PreH10 : (output_size = (Zlength (output_ptrs_2)))) (PreH11 : (plen = (string_length (prefix_l)))) (PreH12 : (out <> 0)) (PreH13 : (data <> 0)) (PreH14 : (rows_well_formed_29 rows strings_size_pre )) (PreH15 : (row_well_formed_29 (Znth (i) (rows) ((@nil Z))) )) (PreH16 : (problem_29_pre_z rows )) (PreH17 : (valid_string prefix_l )) (PreH18 : ((string_length (prefix_l)) < INT_MAX)) (PreH19 : (filter_prefix_state_29 rows prefix_l i output_rows_2 )) ,
  (store_string row_ptr (row_payload_z_29 ((Znth (i) (rows) ((@nil Z))))) )
  **  (store_string prefix_addr prefix_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.missing_i strings_addr strings_size_pre i row_ptr rows )
  **  (((strings_addr + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
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
  &&  “ (plen = (string_length (prefix_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (rows_well_formed_29 rows strings_size_pre ) ” 
  &&  “ (problem_29_pre_z rows ) ” 
  &&  “ (valid_string prefix_l ) ” 
  &&  “ ((string_length (prefix_l)) < INT_MAX) ” 
  &&  “ (row_well_formed_29 (Znth (i) (rows) ((@nil Z))) ) ” 
  &&  “ (prefix_miss_z_29 (row_payload_z_29 ((Znth (i) (rows) ((@nil Z))))) prefix_l ) ” 
  &&  “ (filter_prefix_state_29 rows prefix_l i output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.missing_i strings_addr strings_size_pre i row_ptr rows )
  **  (((strings_addr + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_29 ((Znth (i) (rows) ((@nil Z))))) )
  **  (store_string prefix_addr prefix_l )
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size strings_size_pre )
) \/
(
forall (strings_size_pre: Z) (prefix_l: (@list Z)) (rows: (@list (@list Z))) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (i: Z) (output_size: Z) (plen: Z) (out: Z) (data: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (strncmp_result (row_payload_z_29 ((Znth (i) (rows) ((@nil Z))))) prefix_l plen retval )) (PreH3 : (0 <= ((string_length (prefix_l)) + 1 ))) (PreH4 : (0 <= ((string_length ((row_payload_z_29 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) (PreH5 : (0 <= i)) (PreH6 : (i < strings_size_pre)) (PreH7 : (0 <= output_size)) (PreH8 : (output_size <= i)) (PreH9 : (output_size = (Zlength (output_rows_2)))) (PreH10 : (output_size = (Zlength (output_ptrs_2)))) (PreH11 : (plen = (string_length (prefix_l)))) (PreH12 : (out <> 0)) (PreH13 : (data <> 0)) (PreH14 : (rows_well_formed_29 rows strings_size_pre )) (PreH15 : (row_well_formed_29 (Znth (i) (rows) ((@nil Z))) )) (PreH16 : (problem_29_pre_z rows )) (PreH17 : (valid_string prefix_l )) (PreH18 : ((string_length (prefix_l)) < INT_MAX)) (PreH19 : (filter_prefix_state_29 rows prefix_l i output_rows_2 )) ,
  TT && emp 
|--
  EX (output_rows: (@list (@list Z))) ,
  “ (0 <= i) ” 
  &&  “ (i < strings_size_pre) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= i) ” 
  &&  “ (output_size = (Zlength (output_rows))) ” 
  &&  “ (output_size = (Zlength (output_ptrs_2))) ” 
  &&  “ (plen = (string_length (prefix_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (rows_well_formed_29 rows strings_size_pre ) ” 
  &&  “ (problem_29_pre_z rows ) ” 
  &&  “ (valid_string prefix_l ) ” 
  &&  “ ((string_length (prefix_l)) < INT_MAX) ” 
  &&  “ (row_well_formed_29 (Znth (i) (rows) ((@nil Z))) ) ” 
  &&  “ (prefix_miss_z_29 (row_payload_z_29 ((Znth (i) (rows) ((@nil Z))))) prefix_l ) ” 
  &&  “ (filter_prefix_state_29 rows prefix_l i output_rows ) ”
  &&  emp
).

Definition filter_by_prefix_entail_wit_5_1 := 
(
forall (strings_size_pre: Z) (prefix_addr: Z) (strings_addr: Z) (prefix_l: (@list Z)) (rows: (@list (@list Z))) (row_ptr: Z) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (i: Z) (output_size: Z) (plen: Z) (out: Z) (data: Z) (cmp: Z) (PreH1 : (0 <= ((string_length (prefix_l)) + 1 ))) (PreH2 : (0 <= ((string_length ((row_payload_z_29 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < strings_size_pre)) (PreH5 : (0 <= output_size)) (PreH6 : (output_size <= i)) (PreH7 : (output_size = (Zlength (output_rows_2)))) (PreH8 : (output_size = (Zlength (output_ptrs_2)))) (PreH9 : (plen = (string_length (prefix_l)))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (cmp = 0)) (PreH13 : (rows_well_formed_29 rows strings_size_pre )) (PreH14 : (problem_29_pre_z rows )) (PreH15 : (valid_string prefix_l )) (PreH16 : ((string_length (prefix_l)) < INT_MAX)) (PreH17 : (row_well_formed_29 (Znth (i) (rows) ((@nil Z))) )) (PreH18 : (prefix_hit_z_29 (row_payload_z_29 ((Znth (i) (rows) ((@nil Z))))) prefix_l )) (PreH19 : (filter_prefix_state_29 rows prefix_l i output_rows_2 )) ,
  (PtrArray.seg data 0 (output_size + 1 ) (app (output_ptrs_2) ((cons (row_ptr) ((@nil Z))))) )
  **  (PtrArray.undef_seg data (output_size + 1 ) strings_size_pre )
  **  (CharArray.full prefix_addr ((string_length (prefix_l)) + 1 ) (c_string (prefix_l)) )
  **  (CharArray.full row_ptr ((string_length ((row_payload_z_29 ((Znth (i) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_29 ((Znth (i) (rows) ((@nil Z))))))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.missing_i strings_addr strings_size_pre i row_ptr rows )
  **  (((strings_addr + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= strings_size_pre) ” 
  &&  “ (0 <= (output_size + 1 )) ” 
  &&  “ ((output_size + 1 ) <= (i + 1 )) ” 
  &&  “ ((output_size + 1 ) = (Zlength (output_rows))) ” 
  &&  “ ((output_size + 1 ) = (Zlength (output_ptrs))) ” 
  &&  “ (plen = (string_length (prefix_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (rows_well_formed_29 rows strings_size_pre ) ” 
  &&  “ (problem_29_pre_z rows ) ” 
  &&  “ (valid_string prefix_l ) ” 
  &&  “ ((string_length (prefix_l)) < INT_MAX) ” 
  &&  “ (filter_prefix_state_29 rows prefix_l (i + 1 ) output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.full strings_addr strings_size_pre rows )
  **  (store_string prefix_addr prefix_l )
  **  (PtrArray.seg data 0 (output_size + 1 ) output_ptrs )
  **  (PtrArray.undef_seg data (output_size + 1 ) strings_size_pre )
) \/
(
forall (strings_size_pre: Z) (strings_addr: Z) (prefix_l: (@list Z)) (rows: (@list (@list Z))) (row_ptr: Z) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (i: Z) (output_size: Z) (plen: Z) (out: Z) (data: Z) (cmp: Z) (PreH1 : (0 <= ((string_length (prefix_l)) + 1 ))) (PreH2 : (0 <= ((string_length ((row_payload_z_29 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < strings_size_pre)) (PreH5 : (0 <= output_size)) (PreH6 : (output_size <= i)) (PreH7 : (output_size = (Zlength (output_rows_2)))) (PreH8 : (output_size = (Zlength (output_ptrs_2)))) (PreH9 : (plen = (string_length (prefix_l)))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (cmp = 0)) (PreH13 : (rows_well_formed_29 rows strings_size_pre )) (PreH14 : (problem_29_pre_z rows )) (PreH15 : (valid_string prefix_l )) (PreH16 : ((string_length (prefix_l)) < INT_MAX)) (PreH17 : (row_well_formed_29 (Znth (i) (rows) ((@nil Z))) )) (PreH18 : (prefix_hit_z_29 (row_payload_z_29 ((Znth (i) (rows) ((@nil Z))))) prefix_l )) (PreH19 : (filter_prefix_state_29 rows prefix_l i output_rows_2 )) ,
  (CharArray.full row_ptr ((string_length ((row_payload_z_29 ((Znth (i) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_29 ((Znth (i) (rows) ((@nil Z))))))) )
  **  (CharPtrArray2.missing_i strings_addr strings_size_pre i row_ptr rows )
  **  (((strings_addr + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  EX (output_rows: (@list (@list Z))) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= strings_size_pre) ” 
  &&  “ (0 <= (output_size + 1 )) ” 
  &&  “ ((output_size + 1 ) <= (i + 1 )) ” 
  &&  “ ((output_size + 1 ) = (Zlength (output_rows))) ” 
  &&  “ ((output_size + 1 ) = (Zlength ((app (output_ptrs_2) ((cons (row_ptr) ((@nil Z)))))))) ” 
  &&  “ (plen = (string_length (prefix_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (rows_well_formed_29 rows strings_size_pre ) ” 
  &&  “ (problem_29_pre_z rows ) ” 
  &&  “ (valid_string prefix_l ) ” 
  &&  “ ((string_length (prefix_l)) < INT_MAX) ” 
  &&  “ (filter_prefix_state_29 rows prefix_l (i + 1 ) output_rows ) ”
  &&  (CharPtrArray2.full strings_addr strings_size_pre rows )
).

Definition filter_by_prefix_entail_wit_5_2 := 
(
forall (strings_size_pre: Z) (prefix_addr: Z) (strings_addr: Z) (prefix_l: (@list Z)) (rows: (@list (@list Z))) (row_ptr: Z) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (i: Z) (output_size: Z) (plen: Z) (out: Z) (data: Z) (cmp: Z) (PreH1 : (0 <= i)) (PreH2 : (i < strings_size_pre)) (PreH3 : (0 <= output_size)) (PreH4 : (output_size <= i)) (PreH5 : (output_size = (Zlength (output_rows_2)))) (PreH6 : (output_size = (Zlength (output_ptrs_2)))) (PreH7 : (plen = (string_length (prefix_l)))) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (cmp <> 0)) (PreH11 : (rows_well_formed_29 rows strings_size_pre )) (PreH12 : (problem_29_pre_z rows )) (PreH13 : (valid_string prefix_l )) (PreH14 : ((string_length (prefix_l)) < INT_MAX)) (PreH15 : (row_well_formed_29 (Znth (i) (rows) ((@nil Z))) )) (PreH16 : (prefix_miss_z_29 (row_payload_z_29 ((Znth (i) (rows) ((@nil Z))))) prefix_l )) (PreH17 : (filter_prefix_state_29 rows prefix_l i output_rows_2 )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.missing_i strings_addr strings_size_pre i row_ptr rows )
  **  (((strings_addr + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_29 ((Znth (i) (rows) ((@nil Z))))) )
  **  (store_string prefix_addr prefix_l )
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
  &&  “ (plen = (string_length (prefix_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (rows_well_formed_29 rows strings_size_pre ) ” 
  &&  “ (problem_29_pre_z rows ) ” 
  &&  “ (valid_string prefix_l ) ” 
  &&  “ ((string_length (prefix_l)) < INT_MAX) ” 
  &&  “ (filter_prefix_state_29 rows prefix_l (i + 1 ) output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.full strings_addr strings_size_pre rows )
  **  (store_string prefix_addr prefix_l )
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size strings_size_pre )
) \/
(
forall (strings_size_pre: Z) (strings_addr: Z) (prefix_l: (@list Z)) (rows: (@list (@list Z))) (row_ptr: Z) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (i: Z) (output_size: Z) (plen: Z) (out: Z) (data: Z) (cmp: Z) (PreH1 : (0 <= ((string_length (prefix_l)) + 1 ))) (PreH2 : (0 <= ((string_length ((row_payload_z_29 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < strings_size_pre)) (PreH5 : (0 <= output_size)) (PreH6 : (output_size <= i)) (PreH7 : (output_size = (Zlength (output_rows_2)))) (PreH8 : (output_size = (Zlength (output_ptrs_2)))) (PreH9 : (plen = (string_length (prefix_l)))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (cmp <> 0)) (PreH13 : (rows_well_formed_29 rows strings_size_pre )) (PreH14 : (problem_29_pre_z rows )) (PreH15 : (valid_string prefix_l )) (PreH16 : ((string_length (prefix_l)) < INT_MAX)) (PreH17 : (row_well_formed_29 (Znth (i) (rows) ((@nil Z))) )) (PreH18 : (prefix_miss_z_29 (row_payload_z_29 ((Znth (i) (rows) ((@nil Z))))) prefix_l )) (PreH19 : (filter_prefix_state_29 rows prefix_l i output_rows_2 )) ,
  (CharArray.full row_ptr ((string_length ((row_payload_z_29 ((Znth (i) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_29 ((Znth (i) (rows) ((@nil Z))))))) )
  **  (CharPtrArray2.missing_i strings_addr strings_size_pre i row_ptr rows )
  **  (((strings_addr + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  EX (output_rows: (@list (@list Z))) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= strings_size_pre) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= (i + 1 )) ” 
  &&  “ (output_size = (Zlength (output_rows))) ” 
  &&  “ (output_size = (Zlength (output_ptrs_2))) ” 
  &&  “ (plen = (string_length (prefix_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (rows_well_formed_29 rows strings_size_pre ) ” 
  &&  “ (problem_29_pre_z rows ) ” 
  &&  “ (valid_string prefix_l ) ” 
  &&  “ ((string_length (prefix_l)) < INT_MAX) ” 
  &&  “ (filter_prefix_state_29 rows prefix_l (i + 1 ) output_rows ) ”
  &&  (CharPtrArray2.full strings_addr strings_size_pre rows )
).

Definition filter_by_prefix_entail_wit_6 := 
(
forall (strings_size_pre: Z) (prefix_addr: Z) (strings_addr: Z) (prefix_l: (@list Z)) (rows: (@list (@list Z))) (data: Z) (out: Z) (plen: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (output_size: Z) (i: Z) (PreH1 : (i >= strings_size_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= strings_size_pre)) (PreH4 : (0 <= output_size)) (PreH5 : (output_size <= i)) (PreH6 : (output_size = (Zlength (output_rows_2)))) (PreH7 : (output_size = (Zlength (output_ptrs_2)))) (PreH8 : (plen = (string_length (prefix_l)))) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (rows_well_formed_29 rows strings_size_pre )) (PreH12 : (problem_29_pre_z rows )) (PreH13 : (valid_string prefix_l )) (PreH14 : ((string_length (prefix_l)) < INT_MAX)) (PreH15 : (filter_prefix_state_29 rows prefix_l i output_rows_2 )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.full strings_addr strings_size_pre rows )
  **  (store_string prefix_addr prefix_l )
  **  (PtrArray.seg data 0 output_size output_ptrs_2 )
  **  (PtrArray.undef_seg data output_size strings_size_pre )
|--
  EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
  “ (0 <= output_size) ” 
  &&  “ (output_size <= strings_size_pre) ” 
  &&  “ (output_size = (Zlength (output_rows))) ” 
  &&  “ (output_size = (Zlength (output_ptrs))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (plen = (string_length (prefix_l))) ” 
  &&  “ (rows_well_formed_29 rows strings_size_pre ) ” 
  &&  “ (problem_29_pre_z rows ) ” 
  &&  “ (valid_string prefix_l ) ” 
  &&  “ (filter_prefix_state_29 rows prefix_l strings_size_pre output_rows ) ” 
  &&  “ (problem_29_spec_z rows prefix_l output_rows ) ”
  &&  ((( &( "i" ) )) # Int  |-> strings_size_pre)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.full strings_addr strings_size_pre rows )
  **  (store_string prefix_addr prefix_l )
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size strings_size_pre )
) \/
(
forall (strings_size_pre: Z) (prefix_l: (@list Z)) (rows: (@list (@list Z))) (data: Z) (out: Z) (plen: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (output_size: Z) (i: Z) (PreH1 : (0 <= ((string_length (prefix_l)) + 1 ))) (PreH2 : (i >= strings_size_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= strings_size_pre)) (PreH5 : (0 <= output_size)) (PreH6 : (output_size <= i)) (PreH7 : (output_size = (Zlength (output_rows_2)))) (PreH8 : (output_size = (Zlength (output_ptrs_2)))) (PreH9 : (plen = (string_length (prefix_l)))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (rows_well_formed_29 rows strings_size_pre )) (PreH13 : (problem_29_pre_z rows )) (PreH14 : (valid_string prefix_l )) (PreH15 : ((string_length (prefix_l)) < INT_MAX)) (PreH16 : (filter_prefix_state_29 rows prefix_l i output_rows_2 )) ,
  TT && emp 
|--
  EX (output_rows: (@list (@list Z))) ,
  “ (i = strings_size_pre) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= strings_size_pre) ” 
  &&  “ (output_size = (Zlength (output_rows))) ” 
  &&  “ (output_size = (Zlength (output_ptrs_2))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (plen = (string_length (prefix_l))) ” 
  &&  “ (rows_well_formed_29 rows strings_size_pre ) ” 
  &&  “ (problem_29_pre_z rows ) ” 
  &&  “ (valid_string prefix_l ) ” 
  &&  “ (filter_prefix_state_29 rows prefix_l strings_size_pre output_rows ) ” 
  &&  “ (problem_29_spec_z rows prefix_l output_rows ) ”
  &&  emp
).

Definition filter_by_prefix_return_wit_1 := 
(
forall (strings_size_pre: Z) (prefix_addr: Z) (strings_addr: Z) (prefix_l: (@list Z)) (rows: (@list (@list Z))) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (output_size_2: Z) (out: Z) (data_2: Z) (plen: Z) (PreH1 : (0 <= output_size_2)) (PreH2 : (output_size_2 <= strings_size_pre)) (PreH3 : (output_size_2 = (Zlength (output_rows_2)))) (PreH4 : (output_size_2 = (Zlength (output_ptrs_2)))) (PreH5 : (out <> 0)) (PreH6 : (data_2 <> 0)) (PreH7 : (plen = (string_length (prefix_l)))) (PreH8 : (rows_well_formed_29 rows strings_size_pre )) (PreH9 : (problem_29_pre_z rows )) (PreH10 : (valid_string prefix_l )) (PreH11 : (filter_prefix_state_29 rows prefix_l strings_size_pre output_rows_2 )) (PreH12 : (problem_29_spec_z rows prefix_l output_rows_2 )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data_2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size_2)
  **  (CharPtrArray2.full strings_addr strings_size_pre rows )
  **  (store_string prefix_addr prefix_l )
  **  (PtrArray.seg data_2 0 output_size_2 output_ptrs_2 )
  **  (PtrArray.undef_seg data_2 output_size_2 strings_size_pre )
|--
  EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z)))  (output_size: Z)  (data: Z) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= strings_size_pre) ” 
  &&  “ (output_size = (Zlength (output_rows))) ” 
  &&  “ (output_size = (Zlength (output_ptrs))) ” 
  &&  “ (problem_29_spec_z rows prefix_l output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (CharPtrArray2.full strings_addr strings_size_pre rows )
  **  (store_string prefix_addr prefix_l )
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size strings_size_pre )
) \/
(
forall (strings_size_pre: Z) (prefix_l: (@list Z)) (rows: (@list (@list Z))) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (output_size_2: Z) (out: Z) (data_2: Z) (plen: Z) (PreH1 : (0 <= ((string_length (prefix_l)) + 1 ))) (PreH2 : (0 <= output_size_2)) (PreH3 : (output_size_2 <= strings_size_pre)) (PreH4 : (output_size_2 = (Zlength (output_rows_2)))) (PreH5 : (output_size_2 = (Zlength (output_ptrs_2)))) (PreH6 : (out <> 0)) (PreH7 : (data_2 <> 0)) (PreH8 : (plen = (string_length (prefix_l)))) (PreH9 : (rows_well_formed_29 rows strings_size_pre )) (PreH10 : (problem_29_pre_z rows )) (PreH11 : (valid_string prefix_l )) (PreH12 : (filter_prefix_state_29 rows prefix_l strings_size_pre output_rows_2 )) (PreH13 : (problem_29_spec_z rows prefix_l output_rows_2 )) ,
  (PtrArray.seg data_2 0 output_size_2 output_ptrs_2 )
  **  (PtrArray.undef_seg data_2 output_size_2 strings_size_pre )
|--
  EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
  “ (output_size_2 = (Zlength (output_rows))) ” 
  &&  “ (output_size_2 = (Zlength (output_rows))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data_2 <> 0) ” 
  &&  “ (0 <= (Zlength (output_rows))) ” 
  &&  “ ((Zlength (output_rows)) <= strings_size_pre) ” 
  &&  “ ((Zlength (output_rows)) = (Zlength (output_ptrs))) ” 
  &&  “ (problem_29_spec_z rows prefix_l output_rows ) ”
  &&  (PtrArray.seg data_2 0 (Zlength (output_rows)) output_ptrs )
  **  (PtrArray.undef_seg data_2 (Zlength (output_rows)) strings_size_pre )
).

Definition filter_by_prefix_partial_solve_wit_1 := 
forall (prefix_pre: Z) (strings_size_pre: Z) (strings_pre: Z) (prefix_addr: Z) (strings_addr: Z) (prefix_l: (@list Z)) (rows: (@list (@list Z))) (PreH1 : (strings_pre = strings_addr)) (PreH2 : (prefix_pre = prefix_addr)) (PreH3 : (0 <= strings_size_pre)) (PreH4 : (strings_size_pre < INT_MAX)) (PreH5 : (rows_well_formed_29 rows strings_size_pre )) (PreH6 : (problem_29_pre_z rows )) (PreH7 : (valid_string prefix_l )) (PreH8 : ((string_length (prefix_l)) < INT_MAX)) ,
  (CharPtrArray2.full strings_pre strings_size_pre rows )
  **  (store_string prefix_pre prefix_l )
|--
  “ (0 <= ((string_length (prefix_l)) + 1 )) ” 
  &&  “ (strings_pre = strings_addr) ” 
  &&  “ (prefix_pre = prefix_addr) ” 
  &&  “ (0 <= strings_size_pre) ” 
  &&  “ (strings_size_pre < INT_MAX) ” 
  &&  “ (rows_well_formed_29 rows strings_size_pre ) ” 
  &&  “ (problem_29_pre_z rows ) ” 
  &&  “ (valid_string prefix_l ) ” 
  &&  “ ((string_length (prefix_l)) < INT_MAX) ”
  &&  (CharArray.full prefix_pre ((string_length (prefix_l)) + 1 ) (c_string (prefix_l)) )
  **  (CharPtrArray2.full strings_pre strings_size_pre rows )
.

Definition filter_by_prefix_partial_solve_wit_2_pure := 
forall (prefix_pre: Z) (strings_size_pre: Z) (strings_pre: Z) (prefix_addr: Z) (strings_addr: Z) (prefix_l: (@list Z)) (rows: (@list (@list Z))) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (prefix_l)) + 1 ))) (PreH3 : (strings_pre = strings_addr)) (PreH4 : (prefix_pre = prefix_addr)) (PreH5 : (0 <= strings_size_pre)) (PreH6 : (strings_size_pre < INT_MAX)) (PreH7 : (rows_well_formed_29 rows strings_size_pre )) (PreH8 : (problem_29_pre_z rows )) (PreH9 : (valid_string prefix_l )) (PreH10 : ((string_length (prefix_l)) < INT_MAX)) ,
  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full prefix_pre ((string_length (prefix_l)) + 1 ) (c_string (prefix_l)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "strings_size" ) )) # Int  |-> strings_size_pre)
  **  ((( &( "strings" ) )) # Ptr  |-> strings_pre)
  **  (CharPtrArray2.full strings_pre strings_size_pre rows )
|--
  “ (0 <= strings_size_pre) ” 
  &&  “ (strings_size_pre < INT_MAX) ”
.

Definition filter_by_prefix_partial_solve_wit_2_aux := 
forall (prefix_pre: Z) (strings_size_pre: Z) (strings_pre: Z) (prefix_addr: Z) (strings_addr: Z) (prefix_l: (@list Z)) (rows: (@list (@list Z))) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (prefix_l)) + 1 ))) (PreH3 : (strings_pre = strings_addr)) (PreH4 : (prefix_pre = prefix_addr)) (PreH5 : (0 <= strings_size_pre)) (PreH6 : (strings_size_pre < INT_MAX)) (PreH7 : (rows_well_formed_29 rows strings_size_pre )) (PreH8 : (problem_29_pre_z rows )) (PreH9 : (valid_string prefix_l )) (PreH10 : ((string_length (prefix_l)) < INT_MAX)) ,
  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full prefix_pre ((string_length (prefix_l)) + 1 ) (c_string (prefix_l)) )
  **  (CharPtrArray2.full strings_pre strings_size_pre rows )
|--
  “ (0 <= strings_size_pre) ” 
  &&  “ (strings_size_pre < INT_MAX) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= ((string_length (prefix_l)) + 1 )) ” 
  &&  “ (strings_pre = strings_addr) ” 
  &&  “ (prefix_pre = prefix_addr) ” 
  &&  “ (0 <= strings_size_pre) ” 
  &&  “ (strings_size_pre < INT_MAX) ” 
  &&  “ (rows_well_formed_29 rows strings_size_pre ) ” 
  &&  “ (problem_29_pre_z rows ) ” 
  &&  “ (valid_string prefix_l ) ” 
  &&  “ ((string_length (prefix_l)) < INT_MAX) ”
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full prefix_pre ((string_length (prefix_l)) + 1 ) (c_string (prefix_l)) )
  **  (CharPtrArray2.full strings_pre strings_size_pre rows )
.

Definition filter_by_prefix_partial_solve_wit_2 := filter_by_prefix_partial_solve_wit_2_pure -> filter_by_prefix_partial_solve_wit_2_aux.

Definition filter_by_prefix_partial_solve_wit_3_pure := 
forall (prefix_pre: Z) (strings_size_pre: Z) (strings_pre: Z) (prefix_addr: Z) (strings_addr: Z) (prefix_l: (@list Z)) (rows: (@list (@list Z))) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= ((string_length (prefix_l)) + 1 ))) (PreH4 : (strings_pre = strings_addr)) (PreH5 : (prefix_pre = prefix_addr)) (PreH6 : (0 <= strings_size_pre)) (PreH7 : (strings_size_pre < INT_MAX)) (PreH8 : (rows_well_formed_29 rows strings_size_pre )) (PreH9 : (problem_29_pre_z rows )) (PreH10 : (valid_string prefix_l )) (PreH11 : ((string_length (prefix_l)) < INT_MAX)) ,
  ((( &( "plen" ) )) # Int  |->_)
  **  ((( &( "output_size" ) )) # Int  |-> 0)
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (PtrArray.undef_seg retval_2 0 strings_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full prefix_pre ((string_length (prefix_l)) + 1 ) (c_string (prefix_l)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_pre)
  **  ((( &( "strings_size" ) )) # Int  |-> strings_size_pre)
  **  ((( &( "strings" ) )) # Ptr  |-> strings_pre)
  **  (CharPtrArray2.full strings_pre strings_size_pre rows )
|--
  “ (valid_string prefix_l ) ” 
  &&  “ ((string_length (prefix_l)) < INT_MAX) ”
.

Definition filter_by_prefix_partial_solve_wit_3_aux := 
forall (prefix_pre: Z) (strings_size_pre: Z) (strings_pre: Z) (prefix_addr: Z) (strings_addr: Z) (prefix_l: (@list Z)) (rows: (@list (@list Z))) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= ((string_length (prefix_l)) + 1 ))) (PreH4 : (strings_pre = strings_addr)) (PreH5 : (prefix_pre = prefix_addr)) (PreH6 : (0 <= strings_size_pre)) (PreH7 : (strings_size_pre < INT_MAX)) (PreH8 : (rows_well_formed_29 rows strings_size_pre )) (PreH9 : (problem_29_pre_z rows )) (PreH10 : (valid_string prefix_l )) (PreH11 : ((string_length (prefix_l)) < INT_MAX)) ,
  (PtrArray.undef_seg retval_2 0 strings_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full prefix_pre ((string_length (prefix_l)) + 1 ) (c_string (prefix_l)) )
  **  (CharPtrArray2.full strings_pre strings_size_pre rows )
|--
  “ (valid_string prefix_l ) ” 
  &&  “ ((string_length (prefix_l)) < INT_MAX) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= ((string_length (prefix_l)) + 1 )) ” 
  &&  “ (strings_pre = strings_addr) ” 
  &&  “ (prefix_pre = prefix_addr) ” 
  &&  “ (0 <= strings_size_pre) ” 
  &&  “ (strings_size_pre < INT_MAX) ” 
  &&  “ (rows_well_formed_29 rows strings_size_pre ) ” 
  &&  “ (problem_29_pre_z rows ) ” 
  &&  “ (valid_string prefix_l ) ” 
  &&  “ ((string_length (prefix_l)) < INT_MAX) ”
  &&  (store_string prefix_pre prefix_l )
  **  (PtrArray.undef_seg retval_2 0 strings_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.full strings_pre strings_size_pre rows )
.

Definition filter_by_prefix_partial_solve_wit_3 := filter_by_prefix_partial_solve_wit_3_pure -> filter_by_prefix_partial_solve_wit_3_aux.

Definition filter_by_prefix_partial_solve_wit_4_pure := 
(
forall (strings_size_pre: Z) (prefix_addr: Z) (strings_addr: Z) (prefix_l: (@list Z)) (rows: (@list (@list Z))) (row_ptr: Z) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (i: Z) (output_size: Z) (plen: Z) (out: Z) (data: Z) (cmp: Z) (PreH1 : (0 <= i)) (PreH2 : (i < strings_size_pre)) (PreH3 : (0 <= output_size)) (PreH4 : (output_size <= i)) (PreH5 : (output_size = (Zlength (output_rows)))) (PreH6 : (output_size = (Zlength (output_ptrs)))) (PreH7 : (plen = (string_length (prefix_l)))) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (rows_well_formed_29 rows strings_size_pre )) (PreH11 : (row_well_formed_29 (Znth (i) (rows) ((@nil Z))) )) (PreH12 : (problem_29_pre_z rows )) (PreH13 : (valid_string prefix_l )) (PreH14 : ((string_length (prefix_l)) < INT_MAX)) (PreH15 : (filter_prefix_state_29 rows prefix_l i output_rows )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "strings" ) )) # Ptr  |-> strings_addr)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_addr)
  **  ((( &( "strings_size" ) )) # Int  |-> strings_size_pre)
  **  ((( &( "plen" ) )) # Int  |-> plen)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.missing_i strings_addr strings_size_pre i row_ptr rows )
  **  (((strings_addr + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_29 ((Znth (i) (rows) ((@nil Z))))) )
  **  (store_string prefix_addr prefix_l )
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size strings_size_pre )
|--
  “ (valid_string prefix_l ) ” 
  &&  “ (plen < INT_MAX) ” 
  &&  “ ((string_length (prefix_l)) < INT_MAX) ” 
  &&  “ ((string_length ((row_payload_z_29 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX) ” 
  &&  “ (0 <= plen) ” 
  &&  “ (valid_string (row_payload_z_29 ((Znth (i) (rows) ((@nil Z))))) ) ”
) \/
(
forall (strings_size_pre: Z) (prefix_addr: Z) (strings_addr: Z) (prefix_l: (@list Z)) (rows: (@list (@list Z))) (row_ptr: Z) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (i: Z) (output_size: Z) (plen: Z) (out: Z) (data: Z) (cmp: Z) (PreH1 : (0 <= INT_MAX)) (PreH2 : (cmp <= INT_MAX)) (PreH3 : (plen <= INT_MAX)) (PreH4 : (strings_size_pre <= INT_MAX)) (PreH5 : (output_size <= INT_MAX)) (PreH6 : (i <= INT_MAX)) (PreH7 : (0 >= INT_MIN)) (PreH8 : (cmp >= INT_MIN)) (PreH9 : (plen >= INT_MIN)) (PreH10 : (strings_size_pre >= INT_MIN)) (PreH11 : (output_size >= INT_MIN)) (PreH12 : (i >= INT_MIN)) (PreH13 : (0 <= ((string_length (prefix_l)) + 1 ))) (PreH14 : (0 <= ((string_length ((row_payload_z_29 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) (PreH15 : (0 <= i)) (PreH16 : (i < strings_size_pre)) (PreH17 : (0 <= output_size)) (PreH18 : (output_size <= i)) (PreH19 : (output_size = (Zlength (output_rows)))) (PreH20 : (output_size = (Zlength (output_ptrs)))) (PreH21 : (plen = (string_length (prefix_l)))) (PreH22 : (out <> 0)) (PreH23 : (data <> 0)) (PreH24 : (rows_well_formed_29 rows strings_size_pre )) (PreH25 : (row_well_formed_29 (Znth (i) (rows) ((@nil Z))) )) (PreH26 : (problem_29_pre_z rows )) (PreH27 : (valid_string prefix_l )) (PreH28 : ((string_length (prefix_l)) < INT_MAX)) (PreH29 : (filter_prefix_state_29 rows prefix_l i output_rows )) ,
  (CharArray.full prefix_addr ((string_length (prefix_l)) + 1 ) (c_string (prefix_l)) )
  **  (CharArray.full row_ptr ((string_length ((row_payload_z_29 ((Znth (i) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_29 ((Znth (i) (rows) ((@nil Z))))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "strings" ) )) # Ptr  |-> strings_addr)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_addr)
  **  ((( &( "strings_size" ) )) # Int  |-> strings_size_pre)
  **  ((( &( "plen" ) )) # Int  |-> plen)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.missing_i strings_addr strings_size_pre i row_ptr rows )
  **  (((strings_addr + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size strings_size_pre )
|--
  “ (valid_string (row_payload_z_29 ((Znth (i) (rows) ((@nil Z))))) ) ” 
  &&  “ (0 <= plen) ” 
  &&  “ ((string_length ((row_payload_z_29 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX) ”
).

Definition filter_by_prefix_partial_solve_wit_4_pure_split_goal_1 := 
forall (strings_size_pre: Z) (prefix_addr: Z) (strings_addr: Z) (prefix_l: (@list Z)) (rows: (@list (@list Z))) (row_ptr: Z) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (i: Z) (output_size: Z) (plen: Z) (out: Z) (data: Z) (cmp: Z) (PreH1 : (0 <= INT_MAX)) (PreH2 : (cmp <= INT_MAX)) (PreH3 : (plen <= INT_MAX)) (PreH4 : (strings_size_pre <= INT_MAX)) (PreH5 : (output_size <= INT_MAX)) (PreH6 : (i <= INT_MAX)) (PreH7 : (0 >= INT_MIN)) (PreH8 : (cmp >= INT_MIN)) (PreH9 : (plen >= INT_MIN)) (PreH10 : (strings_size_pre >= INT_MIN)) (PreH11 : (output_size >= INT_MIN)) (PreH12 : (i >= INT_MIN)) (PreH13 : (0 <= ((string_length (prefix_l)) + 1 ))) (PreH14 : (0 <= ((string_length ((row_payload_z_29 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) (PreH15 : (0 <= i)) (PreH16 : (i < strings_size_pre)) (PreH17 : (0 <= output_size)) (PreH18 : (output_size <= i)) (PreH19 : (output_size = (Zlength (output_rows)))) (PreH20 : (output_size = (Zlength (output_ptrs)))) (PreH21 : (plen = (string_length (prefix_l)))) (PreH22 : (out <> 0)) (PreH23 : (data <> 0)) (PreH24 : (rows_well_formed_29 rows strings_size_pre )) (PreH25 : (row_well_formed_29 (Znth (i) (rows) ((@nil Z))) )) (PreH26 : (problem_29_pre_z rows )) (PreH27 : (valid_string prefix_l )) (PreH28 : ((string_length (prefix_l)) < INT_MAX)) (PreH29 : (filter_prefix_state_29 rows prefix_l i output_rows )) ,
  (CharArray.full prefix_addr ((string_length (prefix_l)) + 1 ) (c_string (prefix_l)) )
  **  (CharArray.full row_ptr ((string_length ((row_payload_z_29 ((Znth (i) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_29 ((Znth (i) (rows) ((@nil Z))))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "strings" ) )) # Ptr  |-> strings_addr)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_addr)
  **  ((( &( "strings_size" ) )) # Int  |-> strings_size_pre)
  **  ((( &( "plen" ) )) # Int  |-> plen)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.missing_i strings_addr strings_size_pre i row_ptr rows )
  **  (((strings_addr + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size strings_size_pre )
|--
  “ (valid_string (row_payload_z_29 ((Znth (i) (rows) ((@nil Z))))) ) ”
.

Definition filter_by_prefix_partial_solve_wit_4_pure_split_goal_2 := 
forall (strings_size_pre: Z) (prefix_addr: Z) (strings_addr: Z) (prefix_l: (@list Z)) (rows: (@list (@list Z))) (row_ptr: Z) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (i: Z) (output_size: Z) (plen: Z) (out: Z) (data: Z) (cmp: Z) (PreH1 : (0 <= INT_MAX)) (PreH2 : (cmp <= INT_MAX)) (PreH3 : (plen <= INT_MAX)) (PreH4 : (strings_size_pre <= INT_MAX)) (PreH5 : (output_size <= INT_MAX)) (PreH6 : (i <= INT_MAX)) (PreH7 : (0 >= INT_MIN)) (PreH8 : (cmp >= INT_MIN)) (PreH9 : (plen >= INT_MIN)) (PreH10 : (strings_size_pre >= INT_MIN)) (PreH11 : (output_size >= INT_MIN)) (PreH12 : (i >= INT_MIN)) (PreH13 : (0 <= ((string_length (prefix_l)) + 1 ))) (PreH14 : (0 <= ((string_length ((row_payload_z_29 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) (PreH15 : (0 <= i)) (PreH16 : (i < strings_size_pre)) (PreH17 : (0 <= output_size)) (PreH18 : (output_size <= i)) (PreH19 : (output_size = (Zlength (output_rows)))) (PreH20 : (output_size = (Zlength (output_ptrs)))) (PreH21 : (plen = (string_length (prefix_l)))) (PreH22 : (out <> 0)) (PreH23 : (data <> 0)) (PreH24 : (rows_well_formed_29 rows strings_size_pre )) (PreH25 : (row_well_formed_29 (Znth (i) (rows) ((@nil Z))) )) (PreH26 : (problem_29_pre_z rows )) (PreH27 : (valid_string prefix_l )) (PreH28 : ((string_length (prefix_l)) < INT_MAX)) (PreH29 : (filter_prefix_state_29 rows prefix_l i output_rows )) ,
  (CharArray.full prefix_addr ((string_length (prefix_l)) + 1 ) (c_string (prefix_l)) )
  **  (CharArray.full row_ptr ((string_length ((row_payload_z_29 ((Znth (i) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_29 ((Znth (i) (rows) ((@nil Z))))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "strings" ) )) # Ptr  |-> strings_addr)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_addr)
  **  ((( &( "strings_size" ) )) # Int  |-> strings_size_pre)
  **  ((( &( "plen" ) )) # Int  |-> plen)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.missing_i strings_addr strings_size_pre i row_ptr rows )
  **  (((strings_addr + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size strings_size_pre )
|--
  “ (0 <= plen) ”
.

Definition filter_by_prefix_partial_solve_wit_4_pure_split_goal_3 := 
forall (strings_size_pre: Z) (prefix_addr: Z) (strings_addr: Z) (prefix_l: (@list Z)) (rows: (@list (@list Z))) (row_ptr: Z) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (i: Z) (output_size: Z) (plen: Z) (out: Z) (data: Z) (cmp: Z) (PreH1 : (0 <= INT_MAX)) (PreH2 : (cmp <= INT_MAX)) (PreH3 : (plen <= INT_MAX)) (PreH4 : (strings_size_pre <= INT_MAX)) (PreH5 : (output_size <= INT_MAX)) (PreH6 : (i <= INT_MAX)) (PreH7 : (0 >= INT_MIN)) (PreH8 : (cmp >= INT_MIN)) (PreH9 : (plen >= INT_MIN)) (PreH10 : (strings_size_pre >= INT_MIN)) (PreH11 : (output_size >= INT_MIN)) (PreH12 : (i >= INT_MIN)) (PreH13 : (0 <= ((string_length (prefix_l)) + 1 ))) (PreH14 : (0 <= ((string_length ((row_payload_z_29 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) (PreH15 : (0 <= i)) (PreH16 : (i < strings_size_pre)) (PreH17 : (0 <= output_size)) (PreH18 : (output_size <= i)) (PreH19 : (output_size = (Zlength (output_rows)))) (PreH20 : (output_size = (Zlength (output_ptrs)))) (PreH21 : (plen = (string_length (prefix_l)))) (PreH22 : (out <> 0)) (PreH23 : (data <> 0)) (PreH24 : (rows_well_formed_29 rows strings_size_pre )) (PreH25 : (row_well_formed_29 (Znth (i) (rows) ((@nil Z))) )) (PreH26 : (problem_29_pre_z rows )) (PreH27 : (valid_string prefix_l )) (PreH28 : ((string_length (prefix_l)) < INT_MAX)) (PreH29 : (filter_prefix_state_29 rows prefix_l i output_rows )) ,
  (CharArray.full prefix_addr ((string_length (prefix_l)) + 1 ) (c_string (prefix_l)) )
  **  (CharArray.full row_ptr ((string_length ((row_payload_z_29 ((Znth (i) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_29 ((Znth (i) (rows) ((@nil Z))))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "strings" ) )) # Ptr  |-> strings_addr)
  **  ((( &( "prefix" ) )) # Ptr  |-> prefix_addr)
  **  ((( &( "strings_size" ) )) # Int  |-> strings_size_pre)
  **  ((( &( "plen" ) )) # Int  |-> plen)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.missing_i strings_addr strings_size_pre i row_ptr rows )
  **  (((strings_addr + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size strings_size_pre )
|--
  “ ((string_length ((row_payload_z_29 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX) ”
.

Definition filter_by_prefix_partial_solve_wit_4_aux := 
forall (strings_size_pre: Z) (prefix_addr: Z) (strings_addr: Z) (prefix_l: (@list Z)) (rows: (@list (@list Z))) (row_ptr: Z) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (i: Z) (output_size: Z) (plen: Z) (out: Z) (data: Z) (PreH1 : (0 <= i)) (PreH2 : (i < strings_size_pre)) (PreH3 : (0 <= output_size)) (PreH4 : (output_size <= i)) (PreH5 : (output_size = (Zlength (output_rows)))) (PreH6 : (output_size = (Zlength (output_ptrs)))) (PreH7 : (plen = (string_length (prefix_l)))) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (rows_well_formed_29 rows strings_size_pre )) (PreH11 : (row_well_formed_29 (Znth (i) (rows) ((@nil Z))) )) (PreH12 : (problem_29_pre_z rows )) (PreH13 : (valid_string prefix_l )) (PreH14 : ((string_length (prefix_l)) < INT_MAX)) (PreH15 : (filter_prefix_state_29 rows prefix_l i output_rows )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.missing_i strings_addr strings_size_pre i row_ptr rows )
  **  (((strings_addr + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_29 ((Znth (i) (rows) ((@nil Z))))) )
  **  (store_string prefix_addr prefix_l )
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size strings_size_pre )
|--
  “ (valid_string prefix_l ) ” 
  &&  “ (plen < INT_MAX) ” 
  &&  “ ((string_length (prefix_l)) < INT_MAX) ” 
  &&  “ ((string_length ((row_payload_z_29 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX) ” 
  &&  “ (0 <= plen) ” 
  &&  “ (valid_string (row_payload_z_29 ((Znth (i) (rows) ((@nil Z))))) ) ” 
  &&  “ (0 <= ((string_length (prefix_l)) + 1 )) ” 
  &&  “ (0 <= ((string_length ((row_payload_z_29 ((Znth (i) (rows) ((@nil Z))))))) + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < strings_size_pre) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= i) ” 
  &&  “ (output_size = (Zlength (output_rows))) ” 
  &&  “ (output_size = (Zlength (output_ptrs))) ” 
  &&  “ (plen = (string_length (prefix_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (rows_well_formed_29 rows strings_size_pre ) ” 
  &&  “ (row_well_formed_29 (Znth (i) (rows) ((@nil Z))) ) ” 
  &&  “ (problem_29_pre_z rows ) ” 
  &&  “ (valid_string prefix_l ) ” 
  &&  “ ((string_length (prefix_l)) < INT_MAX) ” 
  &&  “ (filter_prefix_state_29 rows prefix_l i output_rows ) ”
  &&  (store_string row_ptr (row_payload_z_29 ((Znth (i) (rows) ((@nil Z))))) )
  **  (store_string prefix_addr prefix_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.missing_i strings_addr strings_size_pre i row_ptr rows )
  **  (((strings_addr + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size strings_size_pre )
.

Definition filter_by_prefix_partial_solve_wit_4 := filter_by_prefix_partial_solve_wit_4_pure -> filter_by_prefix_partial_solve_wit_4_aux.

Definition filter_by_prefix_partial_solve_wit_5 := 
forall (strings_size_pre: Z) (prefix_addr: Z) (strings_addr: Z) (prefix_l: (@list Z)) (rows: (@list (@list Z))) (row_ptr: Z) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (i: Z) (output_size: Z) (plen: Z) (out: Z) (data: Z) (cmp: Z) (PreH1 : (0 <= i)) (PreH2 : (i < strings_size_pre)) (PreH3 : (0 <= output_size)) (PreH4 : (output_size <= i)) (PreH5 : (output_size = (Zlength (output_rows)))) (PreH6 : (output_size = (Zlength (output_ptrs)))) (PreH7 : (plen = (string_length (prefix_l)))) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (cmp = 0)) (PreH11 : (rows_well_formed_29 rows strings_size_pre )) (PreH12 : (problem_29_pre_z rows )) (PreH13 : (valid_string prefix_l )) (PreH14 : ((string_length (prefix_l)) < INT_MAX)) (PreH15 : (row_well_formed_29 (Znth (i) (rows) ((@nil Z))) )) (PreH16 : (prefix_hit_z_29 (row_payload_z_29 ((Znth (i) (rows) ((@nil Z))))) prefix_l )) (PreH17 : (filter_prefix_state_29 rows prefix_l i output_rows )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.missing_i strings_addr strings_size_pre i row_ptr rows )
  **  (((strings_addr + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_29 ((Znth (i) (rows) ((@nil Z))))) )
  **  (store_string prefix_addr prefix_l )
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size strings_size_pre )
|--
  “ (0 <= ((string_length (prefix_l)) + 1 )) ” 
  &&  “ (0 <= ((string_length ((row_payload_z_29 ((Znth (i) (rows) ((@nil Z))))))) + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < strings_size_pre) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= i) ” 
  &&  “ (output_size = (Zlength (output_rows))) ” 
  &&  “ (output_size = (Zlength (output_ptrs))) ” 
  &&  “ (plen = (string_length (prefix_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (cmp = 0) ” 
  &&  “ (rows_well_formed_29 rows strings_size_pre ) ” 
  &&  “ (problem_29_pre_z rows ) ” 
  &&  “ (valid_string prefix_l ) ” 
  &&  “ ((string_length (prefix_l)) < INT_MAX) ” 
  &&  “ (row_well_formed_29 (Znth (i) (rows) ((@nil Z))) ) ” 
  &&  “ (prefix_hit_z_29 (row_payload_z_29 ((Znth (i) (rows) ((@nil Z))))) prefix_l ) ” 
  &&  “ (filter_prefix_state_29 rows prefix_l i output_rows ) ”
  &&  (((data + (output_size * sizeof(PTR) ) )) # Ptr  |->_)
  **  (PtrArray.undef_seg data (output_size + 1 ) strings_size_pre )
  **  (CharArray.full prefix_addr ((string_length (prefix_l)) + 1 ) (c_string (prefix_l)) )
  **  (CharArray.full row_ptr ((string_length ((row_payload_z_29 ((Znth (i) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_29 ((Znth (i) (rows) ((@nil Z))))))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.missing_i strings_addr strings_size_pre i row_ptr rows )
  **  (((strings_addr + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (PtrArray.seg data 0 output_size output_ptrs )
.

Module Type VC_Correct.

Include ptr_array2_Strategy_Correct.
Include char_array_Strategy_Correct.
Include string_Strategy_Correct.

Axiom proof_of_filter_by_prefix_safety_wit_1 : filter_by_prefix_safety_wit_1.
Axiom proof_of_filter_by_prefix_safety_wit_2 : filter_by_prefix_safety_wit_2.
Axiom proof_of_filter_by_prefix_safety_wit_3 : filter_by_prefix_safety_wit_3.
Axiom proof_of_filter_by_prefix_safety_wit_4 : filter_by_prefix_safety_wit_4.
Axiom proof_of_filter_by_prefix_safety_wit_5 : filter_by_prefix_safety_wit_5.
Axiom proof_of_filter_by_prefix_safety_wit_6 : filter_by_prefix_safety_wit_6.
Axiom proof_of_filter_by_prefix_safety_wit_7 : filter_by_prefix_safety_wit_7.
Axiom proof_of_filter_by_prefix_safety_wit_8 : filter_by_prefix_safety_wit_8.
Axiom proof_of_filter_by_prefix_safety_wit_9 : filter_by_prefix_safety_wit_9.
Axiom proof_of_filter_by_prefix_safety_wit_10 : filter_by_prefix_safety_wit_10.
Axiom proof_of_filter_by_prefix_entail_wit_1 : filter_by_prefix_entail_wit_1.
Axiom proof_of_filter_by_prefix_entail_wit_2 : filter_by_prefix_entail_wit_2.
Axiom proof_of_filter_by_prefix_entail_wit_3 : filter_by_prefix_entail_wit_3.
Axiom proof_of_filter_by_prefix_entail_wit_4 : filter_by_prefix_entail_wit_4.
Axiom proof_of_filter_by_prefix_entail_wit_5_1 : filter_by_prefix_entail_wit_5_1.
Axiom proof_of_filter_by_prefix_entail_wit_5_2 : filter_by_prefix_entail_wit_5_2.
Axiom proof_of_filter_by_prefix_entail_wit_6 : filter_by_prefix_entail_wit_6.
Axiom proof_of_filter_by_prefix_return_wit_1 : filter_by_prefix_return_wit_1.
Axiom proof_of_filter_by_prefix_partial_solve_wit_1 : filter_by_prefix_partial_solve_wit_1.
Axiom proof_of_filter_by_prefix_partial_solve_wit_2_pure : filter_by_prefix_partial_solve_wit_2_pure.
Axiom proof_of_filter_by_prefix_partial_solve_wit_2 : filter_by_prefix_partial_solve_wit_2.
Axiom proof_of_filter_by_prefix_partial_solve_wit_3_pure : filter_by_prefix_partial_solve_wit_3_pure.
Axiom proof_of_filter_by_prefix_partial_solve_wit_3 : filter_by_prefix_partial_solve_wit_3.
Axiom proof_of_filter_by_prefix_partial_solve_wit_4_pure : filter_by_prefix_partial_solve_wit_4_pure.
Axiom proof_of_filter_by_prefix_partial_solve_wit_4 : filter_by_prefix_partial_solve_wit_4.
Axiom proof_of_filter_by_prefix_partial_solve_wit_5 : filter_by_prefix_partial_solve_wit_5.

End VC_Correct.
