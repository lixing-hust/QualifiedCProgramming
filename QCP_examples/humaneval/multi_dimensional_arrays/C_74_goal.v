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
Require Import coins_74.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import ptr_array2_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import ptr_array2_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_proof.
Require Import string_strategy_goal.
Require Import string_strategy_proof.

(*----- Function total_match -----*)

Definition total_match_safety_wit_1 := 
forall (lst2_size_pre: Z) (lst2_pre: Z) (lst1_size_pre: Z) (lst1_pre: Z) (rows2: (@list (@list Z))) (rows1: (@list (@list Z))) (PreH1 : (0 <= lst1_size_pre)) (PreH2 : (lst1_size_pre <= 100)) (PreH3 : (0 <= lst2_size_pre)) (PreH4 : (lst2_size_pre <= 100)) (PreH5 : (rows_well_formed_74 rows1 lst1_size_pre )) (PreH6 : (rows_well_formed_74 rows2 lst2_size_pre )) (PreH7 : (problem_74_pre_z rows1 rows2 )) ,
  ((( &( "num1" ) )) # Int  |->_)
  **  ((( &( "lst2_size" ) )) # Int  |-> lst2_size_pre)
  **  ((( &( "lst2" ) )) # Ptr  |-> lst2_pre)
  **  ((( &( "lst1_size" ) )) # Int  |-> lst1_size_pre)
  **  ((( &( "lst1" ) )) # Ptr  |-> lst1_pre)
  **  (CharPtrArray2.full lst1_pre lst1_size_pre rows1 )
  **  (CharPtrArray2.full lst2_pre lst2_size_pre rows2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition total_match_safety_wit_2 := 
forall (lst2_size_pre: Z) (lst2_pre: Z) (lst1_size_pre: Z) (lst1_pre: Z) (rows2: (@list (@list Z))) (rows1: (@list (@list Z))) (PreH1 : (0 <= lst1_size_pre)) (PreH2 : (lst1_size_pre <= 100)) (PreH3 : (0 <= lst2_size_pre)) (PreH4 : (lst2_size_pre <= 100)) (PreH5 : (rows_well_formed_74 rows1 lst1_size_pre )) (PreH6 : (rows_well_formed_74 rows2 lst2_size_pre )) (PreH7 : (problem_74_pre_z rows1 rows2 )) ,
  ((( &( "num2" ) )) # Int  |->_)
  **  ((( &( "num1" ) )) # Int  |-> 0)
  **  ((( &( "lst2_size" ) )) # Int  |-> lst2_size_pre)
  **  ((( &( "lst2" ) )) # Ptr  |-> lst2_pre)
  **  ((( &( "lst1_size" ) )) # Int  |-> lst1_size_pre)
  **  ((( &( "lst1" ) )) # Ptr  |-> lst1_pre)
  **  (CharPtrArray2.full lst1_pre lst1_size_pre rows1 )
  **  (CharPtrArray2.full lst2_pre lst2_size_pre rows2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition total_match_safety_wit_3 := 
forall (lst2_size_pre: Z) (lst2_pre: Z) (lst1_size_pre: Z) (lst1_pre: Z) (rows2: (@list (@list Z))) (rows1: (@list (@list Z))) (PreH1 : (0 <= lst1_size_pre)) (PreH2 : (lst1_size_pre <= 100)) (PreH3 : (0 <= lst2_size_pre)) (PreH4 : (lst2_size_pre <= 100)) (PreH5 : (rows_well_formed_74 rows1 lst1_size_pre )) (PreH6 : (rows_well_formed_74 rows2 lst2_size_pre )) (PreH7 : (problem_74_pre_z rows1 rows2 )) ,
  ((( &( "len" ) )) # Int  |->_)
  **  ((( &( "num2" ) )) # Int  |-> 0)
  **  ((( &( "num1" ) )) # Int  |-> 0)
  **  ((( &( "lst2_size" ) )) # Int  |-> lst2_size_pre)
  **  ((( &( "lst2" ) )) # Ptr  |-> lst2_pre)
  **  ((( &( "lst1_size" ) )) # Int  |-> lst1_size_pre)
  **  ((( &( "lst1" ) )) # Ptr  |-> lst1_pre)
  **  (CharPtrArray2.full lst1_pre lst1_size_pre rows1 )
  **  (CharPtrArray2.full lst2_pre lst2_size_pre rows2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition total_match_safety_wit_4 := 
forall (lst2_size_pre: Z) (lst2_pre: Z) (lst1_size_pre: Z) (lst1_pre: Z) (rows2: (@list (@list Z))) (rows1: (@list (@list Z))) (PreH1 : (0 <= lst1_size_pre)) (PreH2 : (lst1_size_pre <= 100)) (PreH3 : (0 <= lst2_size_pre)) (PreH4 : (lst2_size_pre <= 100)) (PreH5 : (rows_well_formed_74 rows1 lst1_size_pre )) (PreH6 : (rows_well_formed_74 rows2 lst2_size_pre )) (PreH7 : (problem_74_pre_z rows1 rows2 )) ,
  ((( &( "cur" ) )) # Ptr  |->_)
  **  ((( &( "len" ) )) # Int  |-> 0)
  **  ((( &( "num2" ) )) # Int  |-> 0)
  **  ((( &( "num1" ) )) # Int  |-> 0)
  **  ((( &( "lst2_size" ) )) # Int  |-> lst2_size_pre)
  **  ((( &( "lst2" ) )) # Ptr  |-> lst2_pre)
  **  ((( &( "lst1_size" ) )) # Int  |-> lst1_size_pre)
  **  ((( &( "lst1" ) )) # Ptr  |-> lst1_pre)
  **  (CharPtrArray2.full lst1_pre lst1_size_pre rows1 )
  **  (CharPtrArray2.full lst2_pre lst2_size_pre rows2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition total_match_safety_wit_5 := 
forall (lst2_size_pre: Z) (lst2_pre: Z) (lst1_size_pre: Z) (lst1_pre: Z) (rows2: (@list (@list Z))) (rows1: (@list (@list Z))) (PreH1 : (0 <= lst1_size_pre)) (PreH2 : (lst1_size_pre <= 100)) (PreH3 : (0 <= lst2_size_pre)) (PreH4 : (lst2_size_pre <= 100)) (PreH5 : (rows_well_formed_74 rows1 lst1_size_pre )) (PreH6 : (rows_well_formed_74 rows2 lst2_size_pre )) (PreH7 : (problem_74_pre_z rows1 rows2 )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Ptr  |-> 0)
  **  ((( &( "len" ) )) # Int  |-> 0)
  **  ((( &( "num2" ) )) # Int  |-> 0)
  **  ((( &( "num1" ) )) # Int  |-> 0)
  **  ((( &( "lst2_size" ) )) # Int  |-> lst2_size_pre)
  **  ((( &( "lst2" ) )) # Ptr  |-> lst2_pre)
  **  ((( &( "lst1_size" ) )) # Int  |-> lst1_size_pre)
  **  ((( &( "lst1" ) )) # Ptr  |-> lst1_pre)
  **  (CharPtrArray2.full lst1_pre lst1_size_pre rows1 )
  **  (CharPtrArray2.full lst2_pre lst2_size_pre rows2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition total_match_safety_wit_6 := 
(
forall (lst2_size_pre: Z) (lst2_pre: Z) (lst1_size_pre: Z) (lst1_pre: Z) (rows2: (@list (@list Z))) (rows1: (@list (@list Z))) (row_ptr: Z) (i: Z) (num2: Z) (len: Z) (num1: Z) (retval: Z) (PreH1 : (retval = (string_length ((row_payload_z_74 ((Znth (i) (rows1) ((@nil Z))))))))) (PreH2 : (0 <= ((string_length ((row_payload_z_74 ((Znth (i) (rows1) ((@nil Z))))))) + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < lst1_size_pre)) (PreH5 : (num2 = 0)) (PreH6 : (0 <= len)) (PreH7 : (len < INT_MAX)) (PreH8 : (rows_well_formed_74 rows1 lst1_size_pre )) (PreH9 : (rows_well_formed_74 rows2 lst2_size_pre )) (PreH10 : (problem_74_pre_z rows1 rows2 )) (PreH11 : (total_prefix_state_74 rows1 i num1 )) (PreH12 : (valid_string (row_payload_z_74 ((Znth (i) (rows1) ((@nil Z))))) )) (PreH13 : ((string_length ((row_payload_z_74 ((Znth (i) (rows1) ((@nil Z))))))) < INT_MAX)) (PreH14 : ((Zlength ((Znth (i) (rows1) ((@nil Z))))) = ((string_length ((row_payload_z_74 ((Znth (i) (rows1) ((@nil Z))))))) + 1 ))) (PreH15 : (0 <= (rows_total_len_z_74 (rows1)))) (PreH16 : ((rows_total_len_z_74 (rows1)) <= INT_MAX)) (PreH17 : (0 <= (rows_total_len_z_74 (rows2)))) (PreH18 : ((rows_total_len_z_74 (rows2)) <= INT_MAX)) ,
  (store_string row_ptr (row_payload_z_74 ((Znth (i) (rows1) ((@nil Z))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lst1_size" ) )) # Int  |-> lst1_size_pre)
  **  ((( &( "lst2_size" ) )) # Int  |-> lst2_size_pre)
  **  ((( &( "lst1" ) )) # Ptr  |-> lst1_pre)
  **  ((( &( "lst2" ) )) # Ptr  |-> lst2_pre)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "len" ) )) # Int  |-> retval)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  (CharPtrArray2.missing_i lst1_pre lst1_size_pre i row_ptr rows1 )
  **  (((lst1_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharPtrArray2.full lst2_pre lst2_size_pre rows2 )
|--
  “ ((num1 + retval ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (num1 + retval )) ”
) \/
(
forall (lst2_size_pre: Z) (lst2_pre: Z) (lst1_size_pre: Z) (lst1_pre: Z) (rows2: (@list (@list Z))) (rows1: (@list (@list Z))) (row_ptr: Z) (i: Z) (num2: Z) (len: Z) (num1: Z) (retval: Z) (PreH1 : (retval = (string_length ((row_payload_z_74 ((Znth (i) (rows1) ((@nil Z))))))))) (PreH2 : (0 <= ((string_length ((row_payload_z_74 ((Znth (i) (rows1) ((@nil Z))))))) + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < lst1_size_pre)) (PreH5 : (num2 = 0)) (PreH6 : (0 <= len)) (PreH7 : (len < INT_MAX)) (PreH8 : (rows_well_formed_74 rows1 lst1_size_pre )) (PreH9 : (rows_well_formed_74 rows2 lst2_size_pre )) (PreH10 : (problem_74_pre_z rows1 rows2 )) (PreH11 : (total_prefix_state_74 rows1 i num1 )) (PreH12 : (valid_string (row_payload_z_74 ((Znth (i) (rows1) ((@nil Z))))) )) (PreH13 : ((string_length ((row_payload_z_74 ((Znth (i) (rows1) ((@nil Z))))))) < INT_MAX)) (PreH14 : ((Zlength ((Znth (i) (rows1) ((@nil Z))))) = ((string_length ((row_payload_z_74 ((Znth (i) (rows1) ((@nil Z))))))) + 1 ))) (PreH15 : (0 <= (rows_total_len_z_74 (rows1)))) (PreH16 : ((rows_total_len_z_74 (rows1)) <= INT_MAX)) (PreH17 : (0 <= (rows_total_len_z_74 (rows2)))) (PreH18 : ((rows_total_len_z_74 (rows2)) <= INT_MAX)) ,
  (store_string row_ptr (row_payload_z_74 ((Znth (i) (rows1) ((@nil Z))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lst1_size" ) )) # Int  |-> lst1_size_pre)
  **  ((( &( "lst2_size" ) )) # Int  |-> lst2_size_pre)
  **  ((( &( "lst1" ) )) # Ptr  |-> lst1_pre)
  **  ((( &( "lst2" ) )) # Ptr  |-> lst2_pre)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "len" ) )) # Int  |-> retval)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  (CharPtrArray2.missing_i lst1_pre lst1_size_pre i row_ptr rows1 )
  **  (((lst1_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharPtrArray2.full lst2_pre lst2_size_pre rows2 )
|--
  “ ((num1 + retval ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (num1 + retval )) ”
).

Definition total_match_safety_wit_6_split_goal_1 := 
forall (lst2_size_pre: Z) (lst2_pre: Z) (lst1_size_pre: Z) (lst1_pre: Z) (rows2: (@list (@list Z))) (rows1: (@list (@list Z))) (row_ptr: Z) (i: Z) (num2: Z) (len: Z) (num1: Z) (retval: Z) (PreH1 : (retval = (string_length ((row_payload_z_74 ((Znth (i) (rows1) ((@nil Z))))))))) (PreH2 : (0 <= ((string_length ((row_payload_z_74 ((Znth (i) (rows1) ((@nil Z))))))) + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < lst1_size_pre)) (PreH5 : (num2 = 0)) (PreH6 : (0 <= len)) (PreH7 : (len < INT_MAX)) (PreH8 : (rows_well_formed_74 rows1 lst1_size_pre )) (PreH9 : (rows_well_formed_74 rows2 lst2_size_pre )) (PreH10 : (problem_74_pre_z rows1 rows2 )) (PreH11 : (total_prefix_state_74 rows1 i num1 )) (PreH12 : (valid_string (row_payload_z_74 ((Znth (i) (rows1) ((@nil Z))))) )) (PreH13 : ((string_length ((row_payload_z_74 ((Znth (i) (rows1) ((@nil Z))))))) < INT_MAX)) (PreH14 : ((Zlength ((Znth (i) (rows1) ((@nil Z))))) = ((string_length ((row_payload_z_74 ((Znth (i) (rows1) ((@nil Z))))))) + 1 ))) (PreH15 : (0 <= (rows_total_len_z_74 (rows1)))) (PreH16 : ((rows_total_len_z_74 (rows1)) <= INT_MAX)) (PreH17 : (0 <= (rows_total_len_z_74 (rows2)))) (PreH18 : ((rows_total_len_z_74 (rows2)) <= INT_MAX)) ,
  (store_string row_ptr (row_payload_z_74 ((Znth (i) (rows1) ((@nil Z))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lst1_size" ) )) # Int  |-> lst1_size_pre)
  **  ((( &( "lst2_size" ) )) # Int  |-> lst2_size_pre)
  **  ((( &( "lst1" ) )) # Ptr  |-> lst1_pre)
  **  ((( &( "lst2" ) )) # Ptr  |-> lst2_pre)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "len" ) )) # Int  |-> retval)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  (CharPtrArray2.missing_i lst1_pre lst1_size_pre i row_ptr rows1 )
  **  (((lst1_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharPtrArray2.full lst2_pre lst2_size_pre rows2 )
|--
  “ ((num1 + retval ) <= INT_MAX) ”
.

Definition total_match_safety_wit_6_split_goal_2 := 
forall (lst2_size_pre: Z) (lst2_pre: Z) (lst1_size_pre: Z) (lst1_pre: Z) (rows2: (@list (@list Z))) (rows1: (@list (@list Z))) (row_ptr: Z) (i: Z) (num2: Z) (len: Z) (num1: Z) (retval: Z) (PreH1 : (retval = (string_length ((row_payload_z_74 ((Znth (i) (rows1) ((@nil Z))))))))) (PreH2 : (0 <= ((string_length ((row_payload_z_74 ((Znth (i) (rows1) ((@nil Z))))))) + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < lst1_size_pre)) (PreH5 : (num2 = 0)) (PreH6 : (0 <= len)) (PreH7 : (len < INT_MAX)) (PreH8 : (rows_well_formed_74 rows1 lst1_size_pre )) (PreH9 : (rows_well_formed_74 rows2 lst2_size_pre )) (PreH10 : (problem_74_pre_z rows1 rows2 )) (PreH11 : (total_prefix_state_74 rows1 i num1 )) (PreH12 : (valid_string (row_payload_z_74 ((Znth (i) (rows1) ((@nil Z))))) )) (PreH13 : ((string_length ((row_payload_z_74 ((Znth (i) (rows1) ((@nil Z))))))) < INT_MAX)) (PreH14 : ((Zlength ((Znth (i) (rows1) ((@nil Z))))) = ((string_length ((row_payload_z_74 ((Znth (i) (rows1) ((@nil Z))))))) + 1 ))) (PreH15 : (0 <= (rows_total_len_z_74 (rows1)))) (PreH16 : ((rows_total_len_z_74 (rows1)) <= INT_MAX)) (PreH17 : (0 <= (rows_total_len_z_74 (rows2)))) (PreH18 : ((rows_total_len_z_74 (rows2)) <= INT_MAX)) ,
  (store_string row_ptr (row_payload_z_74 ((Znth (i) (rows1) ((@nil Z))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lst1_size" ) )) # Int  |-> lst1_size_pre)
  **  ((( &( "lst2_size" ) )) # Int  |-> lst2_size_pre)
  **  ((( &( "lst1" ) )) # Ptr  |-> lst1_pre)
  **  ((( &( "lst2" ) )) # Ptr  |-> lst2_pre)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "len" ) )) # Int  |-> retval)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  (CharPtrArray2.missing_i lst1_pre lst1_size_pre i row_ptr rows1 )
  **  (((lst1_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharPtrArray2.full lst2_pre lst2_size_pre rows2 )
|--
  “ ((INT_MIN) <= (num1 + retval )) ”
.

Definition total_match_safety_wit_7 := 
forall (lst2_size_pre: Z) (lst2_pre: Z) (lst1_size_pre: Z) (lst1_pre: Z) (rows2: (@list (@list Z))) (rows1: (@list (@list Z))) (i: Z) (num2: Z) (cur: Z) (len: Z) (num1: Z) (PreH1 : (0 <= i)) (PreH2 : (i < lst1_size_pre)) (PreH3 : (num2 = 0)) (PreH4 : (0 <= len)) (PreH5 : (len < INT_MAX)) (PreH6 : (rows_well_formed_74 rows1 lst1_size_pre )) (PreH7 : (rows_well_formed_74 rows2 lst2_size_pre )) (PreH8 : (problem_74_pre_z rows1 rows2 )) (PreH9 : (total_prefix_state_74 rows1 (i + 1 ) num1 )) (PreH10 : (0 <= (rows_total_len_z_74 (rows1)))) (PreH11 : ((rows_total_len_z_74 (rows1)) <= INT_MAX)) (PreH12 : (0 <= (rows_total_len_z_74 (rows2)))) (PreH13 : ((rows_total_len_z_74 (rows2)) <= INT_MAX)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lst1_size" ) )) # Int  |-> lst1_size_pre)
  **  ((( &( "lst2_size" ) )) # Int  |-> lst2_size_pre)
  **  ((( &( "lst1" ) )) # Ptr  |-> lst1_pre)
  **  ((( &( "lst2" ) )) # Ptr  |-> lst2_pre)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  (CharPtrArray2.full lst1_pre lst1_size_pre rows1 )
  **  (CharPtrArray2.full lst2_pre lst2_size_pre rows2 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition total_match_safety_wit_8 := 
forall (lst2_size_pre: Z) (lst2_pre: Z) (lst1_size_pre: Z) (lst1_pre: Z) (rows2: (@list (@list Z))) (rows1: (@list (@list Z))) (num1: Z) (len: Z) (cur: Z) (num2: Z) (i: Z) (PreH1 : (i >= lst1_size_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= lst1_size_pre)) (PreH4 : (num2 = 0)) (PreH5 : (0 <= len)) (PreH6 : (len < INT_MAX)) (PreH7 : (rows_well_formed_74 rows1 lst1_size_pre )) (PreH8 : (rows_well_formed_74 rows2 lst2_size_pre )) (PreH9 : (problem_74_pre_z rows1 rows2 )) (PreH10 : (total_prefix_state_74 rows1 i num1 )) (PreH11 : (0 <= (rows_total_len_z_74 (rows1)))) (PreH12 : ((rows_total_len_z_74 (rows1)) <= INT_MAX)) (PreH13 : (0 <= (rows_total_len_z_74 (rows2)))) (PreH14 : ((rows_total_len_z_74 (rows2)) <= INT_MAX)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "lst1_size" ) )) # Int  |-> lst1_size_pre)
  **  ((( &( "lst2_size" ) )) # Int  |-> lst2_size_pre)
  **  ((( &( "lst1" ) )) # Ptr  |-> lst1_pre)
  **  ((( &( "lst2" ) )) # Ptr  |-> lst2_pre)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  (CharPtrArray2.full lst1_pre lst1_size_pre rows1 )
  **  (CharPtrArray2.full lst2_pre lst2_size_pre rows2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition total_match_safety_wit_9 := 
(
forall (lst2_size_pre: Z) (lst2_pre: Z) (lst1_size_pre: Z) (lst1_pre: Z) (rows2: (@list (@list Z))) (rows1: (@list (@list Z))) (row_ptr: Z) (i: Z) (num1: Z) (len: Z) (num2: Z) (retval: Z) (PreH1 : (retval = (string_length ((row_payload_z_74 ((Znth (i) (rows2) ((@nil Z))))))))) (PreH2 : (0 <= ((string_length ((row_payload_z_74 ((Znth (i) (rows2) ((@nil Z))))))) + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < lst2_size_pre)) (PreH5 : (num1 = (rows_total_len_z_74 (rows1)))) (PreH6 : (0 <= len)) (PreH7 : (len < INT_MAX)) (PreH8 : (rows_well_formed_74 rows1 lst1_size_pre )) (PreH9 : (rows_well_formed_74 rows2 lst2_size_pre )) (PreH10 : (problem_74_pre_z rows1 rows2 )) (PreH11 : (total_prefix_state_74 rows2 i num2 )) (PreH12 : (valid_string (row_payload_z_74 ((Znth (i) (rows2) ((@nil Z))))) )) (PreH13 : ((string_length ((row_payload_z_74 ((Znth (i) (rows2) ((@nil Z))))))) < INT_MAX)) (PreH14 : ((Zlength ((Znth (i) (rows2) ((@nil Z))))) = ((string_length ((row_payload_z_74 ((Znth (i) (rows2) ((@nil Z))))))) + 1 ))) (PreH15 : (0 <= (rows_total_len_z_74 (rows1)))) (PreH16 : ((rows_total_len_z_74 (rows1)) <= INT_MAX)) (PreH17 : (0 <= (rows_total_len_z_74 (rows2)))) (PreH18 : ((rows_total_len_z_74 (rows2)) <= INT_MAX)) ,
  (store_string row_ptr (row_payload_z_74 ((Znth (i) (rows2) ((@nil Z))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lst1_size" ) )) # Int  |-> lst1_size_pre)
  **  ((( &( "lst2_size" ) )) # Int  |-> lst2_size_pre)
  **  ((( &( "lst1" ) )) # Ptr  |-> lst1_pre)
  **  ((( &( "lst2" ) )) # Ptr  |-> lst2_pre)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "len" ) )) # Int  |-> retval)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  (CharPtrArray2.full lst1_pre lst1_size_pre rows1 )
  **  (CharPtrArray2.missing_i lst2_pre lst2_size_pre i row_ptr rows2 )
  **  (((lst2_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ ((num2 + retval ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (num2 + retval )) ”
) \/
(
forall (lst2_size_pre: Z) (lst2_pre: Z) (lst1_size_pre: Z) (lst1_pre: Z) (rows2: (@list (@list Z))) (rows1: (@list (@list Z))) (row_ptr: Z) (i: Z) (num1: Z) (len: Z) (num2: Z) (retval: Z) (PreH1 : (retval = (string_length ((row_payload_z_74 ((Znth (i) (rows2) ((@nil Z))))))))) (PreH2 : (0 <= ((string_length ((row_payload_z_74 ((Znth (i) (rows2) ((@nil Z))))))) + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < lst2_size_pre)) (PreH5 : (num1 = (rows_total_len_z_74 (rows1)))) (PreH6 : (0 <= len)) (PreH7 : (len < INT_MAX)) (PreH8 : (rows_well_formed_74 rows1 lst1_size_pre )) (PreH9 : (rows_well_formed_74 rows2 lst2_size_pre )) (PreH10 : (problem_74_pre_z rows1 rows2 )) (PreH11 : (total_prefix_state_74 rows2 i num2 )) (PreH12 : (valid_string (row_payload_z_74 ((Znth (i) (rows2) ((@nil Z))))) )) (PreH13 : ((string_length ((row_payload_z_74 ((Znth (i) (rows2) ((@nil Z))))))) < INT_MAX)) (PreH14 : ((Zlength ((Znth (i) (rows2) ((@nil Z))))) = ((string_length ((row_payload_z_74 ((Znth (i) (rows2) ((@nil Z))))))) + 1 ))) (PreH15 : (0 <= (rows_total_len_z_74 (rows1)))) (PreH16 : ((rows_total_len_z_74 (rows1)) <= INT_MAX)) (PreH17 : (0 <= (rows_total_len_z_74 (rows2)))) (PreH18 : ((rows_total_len_z_74 (rows2)) <= INT_MAX)) ,
  (store_string row_ptr (row_payload_z_74 ((Znth (i) (rows2) ((@nil Z))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lst1_size" ) )) # Int  |-> lst1_size_pre)
  **  ((( &( "lst2_size" ) )) # Int  |-> lst2_size_pre)
  **  ((( &( "lst1" ) )) # Ptr  |-> lst1_pre)
  **  ((( &( "lst2" ) )) # Ptr  |-> lst2_pre)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "len" ) )) # Int  |-> retval)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  (CharPtrArray2.full lst1_pre lst1_size_pre rows1 )
  **  (CharPtrArray2.missing_i lst2_pre lst2_size_pre i row_ptr rows2 )
  **  (((lst2_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ ((num2 + retval ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (num2 + retval )) ”
).

Definition total_match_safety_wit_9_split_goal_1 := 
forall (lst2_size_pre: Z) (lst2_pre: Z) (lst1_size_pre: Z) (lst1_pre: Z) (rows2: (@list (@list Z))) (rows1: (@list (@list Z))) (row_ptr: Z) (i: Z) (num1: Z) (len: Z) (num2: Z) (retval: Z) (PreH1 : (retval = (string_length ((row_payload_z_74 ((Znth (i) (rows2) ((@nil Z))))))))) (PreH2 : (0 <= ((string_length ((row_payload_z_74 ((Znth (i) (rows2) ((@nil Z))))))) + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < lst2_size_pre)) (PreH5 : (num1 = (rows_total_len_z_74 (rows1)))) (PreH6 : (0 <= len)) (PreH7 : (len < INT_MAX)) (PreH8 : (rows_well_formed_74 rows1 lst1_size_pre )) (PreH9 : (rows_well_formed_74 rows2 lst2_size_pre )) (PreH10 : (problem_74_pre_z rows1 rows2 )) (PreH11 : (total_prefix_state_74 rows2 i num2 )) (PreH12 : (valid_string (row_payload_z_74 ((Znth (i) (rows2) ((@nil Z))))) )) (PreH13 : ((string_length ((row_payload_z_74 ((Znth (i) (rows2) ((@nil Z))))))) < INT_MAX)) (PreH14 : ((Zlength ((Znth (i) (rows2) ((@nil Z))))) = ((string_length ((row_payload_z_74 ((Znth (i) (rows2) ((@nil Z))))))) + 1 ))) (PreH15 : (0 <= (rows_total_len_z_74 (rows1)))) (PreH16 : ((rows_total_len_z_74 (rows1)) <= INT_MAX)) (PreH17 : (0 <= (rows_total_len_z_74 (rows2)))) (PreH18 : ((rows_total_len_z_74 (rows2)) <= INT_MAX)) ,
  (store_string row_ptr (row_payload_z_74 ((Znth (i) (rows2) ((@nil Z))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lst1_size" ) )) # Int  |-> lst1_size_pre)
  **  ((( &( "lst2_size" ) )) # Int  |-> lst2_size_pre)
  **  ((( &( "lst1" ) )) # Ptr  |-> lst1_pre)
  **  ((( &( "lst2" ) )) # Ptr  |-> lst2_pre)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "len" ) )) # Int  |-> retval)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  (CharPtrArray2.full lst1_pre lst1_size_pre rows1 )
  **  (CharPtrArray2.missing_i lst2_pre lst2_size_pre i row_ptr rows2 )
  **  (((lst2_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ ((num2 + retval ) <= INT_MAX) ”
.

Definition total_match_safety_wit_9_split_goal_2 := 
forall (lst2_size_pre: Z) (lst2_pre: Z) (lst1_size_pre: Z) (lst1_pre: Z) (rows2: (@list (@list Z))) (rows1: (@list (@list Z))) (row_ptr: Z) (i: Z) (num1: Z) (len: Z) (num2: Z) (retval: Z) (PreH1 : (retval = (string_length ((row_payload_z_74 ((Znth (i) (rows2) ((@nil Z))))))))) (PreH2 : (0 <= ((string_length ((row_payload_z_74 ((Znth (i) (rows2) ((@nil Z))))))) + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < lst2_size_pre)) (PreH5 : (num1 = (rows_total_len_z_74 (rows1)))) (PreH6 : (0 <= len)) (PreH7 : (len < INT_MAX)) (PreH8 : (rows_well_formed_74 rows1 lst1_size_pre )) (PreH9 : (rows_well_formed_74 rows2 lst2_size_pre )) (PreH10 : (problem_74_pre_z rows1 rows2 )) (PreH11 : (total_prefix_state_74 rows2 i num2 )) (PreH12 : (valid_string (row_payload_z_74 ((Znth (i) (rows2) ((@nil Z))))) )) (PreH13 : ((string_length ((row_payload_z_74 ((Znth (i) (rows2) ((@nil Z))))))) < INT_MAX)) (PreH14 : ((Zlength ((Znth (i) (rows2) ((@nil Z))))) = ((string_length ((row_payload_z_74 ((Znth (i) (rows2) ((@nil Z))))))) + 1 ))) (PreH15 : (0 <= (rows_total_len_z_74 (rows1)))) (PreH16 : ((rows_total_len_z_74 (rows1)) <= INT_MAX)) (PreH17 : (0 <= (rows_total_len_z_74 (rows2)))) (PreH18 : ((rows_total_len_z_74 (rows2)) <= INT_MAX)) ,
  (store_string row_ptr (row_payload_z_74 ((Znth (i) (rows2) ((@nil Z))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lst1_size" ) )) # Int  |-> lst1_size_pre)
  **  ((( &( "lst2_size" ) )) # Int  |-> lst2_size_pre)
  **  ((( &( "lst1" ) )) # Ptr  |-> lst1_pre)
  **  ((( &( "lst2" ) )) # Ptr  |-> lst2_pre)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "len" ) )) # Int  |-> retval)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  (CharPtrArray2.full lst1_pre lst1_size_pre rows1 )
  **  (CharPtrArray2.missing_i lst2_pre lst2_size_pre i row_ptr rows2 )
  **  (((lst2_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ ((INT_MIN) <= (num2 + retval )) ”
.

Definition total_match_safety_wit_10 := 
forall (lst2_size_pre: Z) (lst2_pre: Z) (lst1_size_pre: Z) (lst1_pre: Z) (rows2: (@list (@list Z))) (rows1: (@list (@list Z))) (i: Z) (num1: Z) (cur: Z) (len: Z) (num2: Z) (PreH1 : (0 <= i)) (PreH2 : (i < lst2_size_pre)) (PreH3 : (num1 = (rows_total_len_z_74 (rows1)))) (PreH4 : (0 <= len)) (PreH5 : (len < INT_MAX)) (PreH6 : (rows_well_formed_74 rows1 lst1_size_pre )) (PreH7 : (rows_well_formed_74 rows2 lst2_size_pre )) (PreH8 : (problem_74_pre_z rows1 rows2 )) (PreH9 : (total_prefix_state_74 rows2 (i + 1 ) num2 )) (PreH10 : (0 <= (rows_total_len_z_74 (rows1)))) (PreH11 : ((rows_total_len_z_74 (rows1)) <= INT_MAX)) (PreH12 : (0 <= (rows_total_len_z_74 (rows2)))) (PreH13 : ((rows_total_len_z_74 (rows2)) <= INT_MAX)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lst1_size" ) )) # Int  |-> lst1_size_pre)
  **  ((( &( "lst2_size" ) )) # Int  |-> lst2_size_pre)
  **  ((( &( "lst1" ) )) # Ptr  |-> lst1_pre)
  **  ((( &( "lst2" ) )) # Ptr  |-> lst2_pre)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  (CharPtrArray2.full lst1_pre lst1_size_pre rows1 )
  **  (CharPtrArray2.full lst2_pre lst2_size_pre rows2 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition total_match_entail_wit_1 := 
(
forall (lst2_size_pre: Z) (lst2_pre: Z) (lst1_size_pre: Z) (lst1_pre: Z) (rows2: (@list (@list Z))) (rows1: (@list (@list Z))) (PreH1 : (0 <= lst1_size_pre)) (PreH2 : (lst1_size_pre <= 100)) (PreH3 : (0 <= lst2_size_pre)) (PreH4 : (lst2_size_pre <= 100)) (PreH5 : (rows_well_formed_74 rows1 lst1_size_pre )) (PreH6 : (rows_well_formed_74 rows2 lst2_size_pre )) (PreH7 : (problem_74_pre_z rows1 rows2 )) ,
  (CharPtrArray2.full lst1_pre lst1_size_pre rows1 )
  **  (CharPtrArray2.full lst2_pre lst2_size_pre rows2 )
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= lst1_size_pre) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 < INT_MAX) ” 
  &&  “ (rows_well_formed_74 rows1 lst1_size_pre ) ” 
  &&  “ (rows_well_formed_74 rows2 lst2_size_pre ) ” 
  &&  “ (problem_74_pre_z rows1 rows2 ) ” 
  &&  “ (total_prefix_state_74 rows1 0 0 ) ” 
  &&  “ (0 <= (rows_total_len_z_74 (rows1))) ” 
  &&  “ ((rows_total_len_z_74 (rows1)) <= INT_MAX) ” 
  &&  “ (0 <= (rows_total_len_z_74 (rows2))) ” 
  &&  “ ((rows_total_len_z_74 (rows2)) <= INT_MAX) ”
  &&  (CharPtrArray2.full lst1_pre lst1_size_pre rows1 )
  **  (CharPtrArray2.full lst2_pre lst2_size_pre rows2 )
) \/
(
forall (lst2_size_pre: Z) (lst1_size_pre: Z) (rows2: (@list (@list Z))) (rows1: (@list (@list Z))) (PreH1 : (0 <= lst1_size_pre)) (PreH2 : (lst1_size_pre <= 100)) (PreH3 : (0 <= lst2_size_pre)) (PreH4 : (lst2_size_pre <= 100)) (PreH5 : (rows_well_formed_74 rows1 lst1_size_pre )) (PreH6 : (rows_well_formed_74 rows2 lst2_size_pre )) (PreH7 : (problem_74_pre_z rows1 rows2 )) ,
  TT && emp 
|--
  “ ((rows_total_len_z_74 (rows2)) <= INT_MAX) ” 
  &&  “ (0 <= (rows_total_len_z_74 (rows2))) ” 
  &&  “ ((rows_total_len_z_74 (rows1)) <= INT_MAX) ” 
  &&  “ (0 <= (rows_total_len_z_74 (rows1))) ” 
  &&  “ (total_prefix_state_74 rows1 0 0 ) ”
  &&  emp
).

Definition total_match_entail_wit_1_split_goal_1 := 
forall (lst2_size_pre: Z) (lst1_size_pre: Z) (rows2: (@list (@list Z))) (rows1: (@list (@list Z))) (PreH1 : (0 <= lst1_size_pre)) (PreH2 : (lst1_size_pre <= 100)) (PreH3 : (0 <= lst2_size_pre)) (PreH4 : (lst2_size_pre <= 100)) (PreH5 : (rows_well_formed_74 rows1 lst1_size_pre )) (PreH6 : (rows_well_formed_74 rows2 lst2_size_pre )) (PreH7 : (problem_74_pre_z rows1 rows2 )) ,
  TT && emp 
|--
  “ ((rows_total_len_z_74 (rows2)) <= INT_MAX) ”
.

Definition total_match_entail_wit_1_split_goal_2 := 
forall (lst2_size_pre: Z) (lst1_size_pre: Z) (rows2: (@list (@list Z))) (rows1: (@list (@list Z))) (PreH1 : (0 <= lst1_size_pre)) (PreH2 : (lst1_size_pre <= 100)) (PreH3 : (0 <= lst2_size_pre)) (PreH4 : (lst2_size_pre <= 100)) (PreH5 : (rows_well_formed_74 rows1 lst1_size_pre )) (PreH6 : (rows_well_formed_74 rows2 lst2_size_pre )) (PreH7 : (problem_74_pre_z rows1 rows2 )) ,
  TT && emp 
|--
  “ (0 <= (rows_total_len_z_74 (rows2))) ”
.

Definition total_match_entail_wit_1_split_goal_3 := 
forall (lst2_size_pre: Z) (lst1_size_pre: Z) (rows2: (@list (@list Z))) (rows1: (@list (@list Z))) (PreH1 : (0 <= lst1_size_pre)) (PreH2 : (lst1_size_pre <= 100)) (PreH3 : (0 <= lst2_size_pre)) (PreH4 : (lst2_size_pre <= 100)) (PreH5 : (rows_well_formed_74 rows1 lst1_size_pre )) (PreH6 : (rows_well_formed_74 rows2 lst2_size_pre )) (PreH7 : (problem_74_pre_z rows1 rows2 )) ,
  TT && emp 
|--
  “ ((rows_total_len_z_74 (rows1)) <= INT_MAX) ”
.

Definition total_match_entail_wit_1_split_goal_4 := 
forall (lst2_size_pre: Z) (lst1_size_pre: Z) (rows2: (@list (@list Z))) (rows1: (@list (@list Z))) (PreH1 : (0 <= lst1_size_pre)) (PreH2 : (lst1_size_pre <= 100)) (PreH3 : (0 <= lst2_size_pre)) (PreH4 : (lst2_size_pre <= 100)) (PreH5 : (rows_well_formed_74 rows1 lst1_size_pre )) (PreH6 : (rows_well_formed_74 rows2 lst2_size_pre )) (PreH7 : (problem_74_pre_z rows1 rows2 )) ,
  TT && emp 
|--
  “ (0 <= (rows_total_len_z_74 (rows1))) ”
.

Definition total_match_entail_wit_1_split_goal_5 := 
forall (lst2_size_pre: Z) (lst1_size_pre: Z) (rows2: (@list (@list Z))) (rows1: (@list (@list Z))) (PreH1 : (0 <= lst1_size_pre)) (PreH2 : (lst1_size_pre <= 100)) (PreH3 : (0 <= lst2_size_pre)) (PreH4 : (lst2_size_pre <= 100)) (PreH5 : (rows_well_formed_74 rows1 lst1_size_pre )) (PreH6 : (rows_well_formed_74 rows2 lst2_size_pre )) (PreH7 : (problem_74_pre_z rows1 rows2 )) ,
  TT && emp 
|--
  “ (total_prefix_state_74 rows1 0 0 ) ”
.

Definition total_match_entail_wit_2 := 
(
forall (lst2_size_pre: Z) (lst2_pre: Z) (lst1_size_pre: Z) (lst1_pre: Z) (rows2: (@list (@list Z))) (rows1: (@list (@list Z))) (num1: Z) (len: Z) (num2: Z) (i: Z) (PreH1 : (i < lst1_size_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= lst1_size_pre)) (PreH4 : (num2 = 0)) (PreH5 : (0 <= len)) (PreH6 : (len < INT_MAX)) (PreH7 : (rows_well_formed_74 rows1 lst1_size_pre )) (PreH8 : (rows_well_formed_74 rows2 lst2_size_pre )) (PreH9 : (problem_74_pre_z rows1 rows2 )) (PreH10 : (total_prefix_state_74 rows1 i num1 )) (PreH11 : (0 <= (rows_total_len_z_74 (rows1)))) (PreH12 : ((rows_total_len_z_74 (rows1)) <= INT_MAX)) (PreH13 : (0 <= (rows_total_len_z_74 (rows2)))) (PreH14 : ((rows_total_len_z_74 (rows2)) <= INT_MAX)) ,
  (CharPtrArray2.full lst1_pre lst1_size_pre rows1 )
  **  (CharPtrArray2.full lst2_pre lst2_size_pre rows2 )
|--
  EX (row_ptr: Z) ,
  “ (0 <= i) ” 
  &&  “ (i < lst1_size_pre) ” 
  &&  “ (num2 = 0) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (rows_well_formed_74 rows1 lst1_size_pre ) ” 
  &&  “ (rows_well_formed_74 rows2 lst2_size_pre ) ” 
  &&  “ (problem_74_pre_z rows1 rows2 ) ” 
  &&  “ (total_prefix_state_74 rows1 i num1 ) ” 
  &&  “ (valid_string (row_payload_z_74 ((Znth (i) (rows1) ((@nil Z))))) ) ” 
  &&  “ ((string_length ((row_payload_z_74 ((Znth (i) (rows1) ((@nil Z))))))) < INT_MAX) ” 
  &&  “ ((Zlength ((Znth (i) (rows1) ((@nil Z))))) = ((string_length ((row_payload_z_74 ((Znth (i) (rows1) ((@nil Z))))))) + 1 )) ” 
  &&  “ (0 <= (rows_total_len_z_74 (rows1))) ” 
  &&  “ ((rows_total_len_z_74 (rows1)) <= INT_MAX) ” 
  &&  “ (0 <= (rows_total_len_z_74 (rows2))) ” 
  &&  “ ((rows_total_len_z_74 (rows2)) <= INT_MAX) ”
  &&  (CharPtrArray2.missing_i lst1_pre lst1_size_pre i row_ptr rows1 )
  **  (((lst1_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_74 ((Znth (i) (rows1) ((@nil Z))))) )
  **  (CharPtrArray2.full lst2_pre lst2_size_pre rows2 )
) \/
(
forall (lst2_size_pre: Z) (lst1_size_pre: Z) (rows2: (@list (@list Z))) (rows1: (@list (@list Z))) (num1: Z) (len: Z) (num2: Z) (i: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (0 <= (Zlength ((Znth i rows1 __default__List_Z))))) (PreH2 : (i < lst1_size_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= lst1_size_pre)) (PreH5 : (num2 = 0)) (PreH6 : (0 <= len)) (PreH7 : (len < INT_MAX)) (PreH8 : (rows_well_formed_74 rows1 lst1_size_pre )) (PreH9 : (rows_well_formed_74 rows2 lst2_size_pre )) (PreH10 : (problem_74_pre_z rows1 rows2 )) (PreH11 : (total_prefix_state_74 rows1 i num1 )) (PreH12 : (0 <= (rows_total_len_z_74 (rows1)))) (PreH13 : ((rows_total_len_z_74 (rows1)) <= INT_MAX)) (PreH14 : (0 <= (rows_total_len_z_74 (rows2)))) (PreH15 : ((rows_total_len_z_74 (rows2)) <= INT_MAX)) ,
  (CharArray.full row_ptr_2 (Zlength ((Znth i rows1 __default__List_Z))) (Znth i rows1 __default__List_Z) )
|--
  “ ((Zlength ((Znth (i) (rows1) ((@nil Z))))) = ((string_length ((row_payload_z_74 ((Znth (i) (rows1) ((@nil Z))))))) + 1 )) ” 
  &&  “ ((string_length ((row_payload_z_74 ((Znth (i) (rows1) ((@nil Z))))))) < INT_MAX) ” 
  &&  “ (valid_string (row_payload_z_74 ((Znth (i) (rows1) ((@nil Z))))) ) ”
  &&  (CharArray.full row_ptr_2 ((string_length ((row_payload_z_74 ((Znth (i) (rows1) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_74 ((Znth (i) (rows1) ((@nil Z))))))) )
).

Definition total_match_entail_wit_2_split_goal_1 := 
forall (lst2_size_pre: Z) (lst1_size_pre: Z) (rows2: (@list (@list Z))) (rows1: (@list (@list Z))) (num1: Z) (len: Z) (num2: Z) (i: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (0 <= (Zlength ((Znth i rows1 __default__List_Z))))) (PreH2 : (i < lst1_size_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= lst1_size_pre)) (PreH5 : (num2 = 0)) (PreH6 : (0 <= len)) (PreH7 : (len < INT_MAX)) (PreH8 : (rows_well_formed_74 rows1 lst1_size_pre )) (PreH9 : (rows_well_formed_74 rows2 lst2_size_pre )) (PreH10 : (problem_74_pre_z rows1 rows2 )) (PreH11 : (total_prefix_state_74 rows1 i num1 )) (PreH12 : (0 <= (rows_total_len_z_74 (rows1)))) (PreH13 : ((rows_total_len_z_74 (rows1)) <= INT_MAX)) (PreH14 : (0 <= (rows_total_len_z_74 (rows2)))) (PreH15 : ((rows_total_len_z_74 (rows2)) <= INT_MAX)) ,
  (CharArray.full row_ptr_2 (Zlength ((Znth i rows1 __default__List_Z))) (Znth i rows1 __default__List_Z) )
|--
  “ ((Zlength ((Znth (i) (rows1) ((@nil Z))))) = ((string_length ((row_payload_z_74 ((Znth (i) (rows1) ((@nil Z))))))) + 1 )) ”
.

Definition total_match_entail_wit_2_split_goal_2 := 
forall (lst2_size_pre: Z) (lst1_size_pre: Z) (rows2: (@list (@list Z))) (rows1: (@list (@list Z))) (num1: Z) (len: Z) (num2: Z) (i: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (0 <= (Zlength ((Znth i rows1 __default__List_Z))))) (PreH2 : (i < lst1_size_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= lst1_size_pre)) (PreH5 : (num2 = 0)) (PreH6 : (0 <= len)) (PreH7 : (len < INT_MAX)) (PreH8 : (rows_well_formed_74 rows1 lst1_size_pre )) (PreH9 : (rows_well_formed_74 rows2 lst2_size_pre )) (PreH10 : (problem_74_pre_z rows1 rows2 )) (PreH11 : (total_prefix_state_74 rows1 i num1 )) (PreH12 : (0 <= (rows_total_len_z_74 (rows1)))) (PreH13 : ((rows_total_len_z_74 (rows1)) <= INT_MAX)) (PreH14 : (0 <= (rows_total_len_z_74 (rows2)))) (PreH15 : ((rows_total_len_z_74 (rows2)) <= INT_MAX)) ,
  (CharArray.full row_ptr_2 (Zlength ((Znth i rows1 __default__List_Z))) (Znth i rows1 __default__List_Z) )
|--
  “ ((string_length ((row_payload_z_74 ((Znth (i) (rows1) ((@nil Z))))))) < INT_MAX) ”
.

Definition total_match_entail_wit_2_split_goal_3 := 
forall (lst2_size_pre: Z) (lst1_size_pre: Z) (rows2: (@list (@list Z))) (rows1: (@list (@list Z))) (num1: Z) (len: Z) (num2: Z) (i: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (0 <= (Zlength ((Znth i rows1 __default__List_Z))))) (PreH2 : (i < lst1_size_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= lst1_size_pre)) (PreH5 : (num2 = 0)) (PreH6 : (0 <= len)) (PreH7 : (len < INT_MAX)) (PreH8 : (rows_well_formed_74 rows1 lst1_size_pre )) (PreH9 : (rows_well_formed_74 rows2 lst2_size_pre )) (PreH10 : (problem_74_pre_z rows1 rows2 )) (PreH11 : (total_prefix_state_74 rows1 i num1 )) (PreH12 : (0 <= (rows_total_len_z_74 (rows1)))) (PreH13 : ((rows_total_len_z_74 (rows1)) <= INT_MAX)) (PreH14 : (0 <= (rows_total_len_z_74 (rows2)))) (PreH15 : ((rows_total_len_z_74 (rows2)) <= INT_MAX)) ,
  (CharArray.full row_ptr_2 (Zlength ((Znth i rows1 __default__List_Z))) (Znth i rows1 __default__List_Z) )
|--
  “ (valid_string (row_payload_z_74 ((Znth (i) (rows1) ((@nil Z))))) ) ”
.

Definition total_match_entail_wit_2_split_goal_spatial := 
forall (lst2_size_pre: Z) (lst1_size_pre: Z) (rows2: (@list (@list Z))) (rows1: (@list (@list Z))) (num1: Z) (len: Z) (num2: Z) (i: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (0 <= (Zlength ((Znth i rows1 __default__List_Z))))) (PreH2 : (i < lst1_size_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= lst1_size_pre)) (PreH5 : (num2 = 0)) (PreH6 : (0 <= len)) (PreH7 : (len < INT_MAX)) (PreH8 : (rows_well_formed_74 rows1 lst1_size_pre )) (PreH9 : (rows_well_formed_74 rows2 lst2_size_pre )) (PreH10 : (problem_74_pre_z rows1 rows2 )) (PreH11 : (total_prefix_state_74 rows1 i num1 )) (PreH12 : (0 <= (rows_total_len_z_74 (rows1)))) (PreH13 : ((rows_total_len_z_74 (rows1)) <= INT_MAX)) (PreH14 : (0 <= (rows_total_len_z_74 (rows2)))) (PreH15 : ((rows_total_len_z_74 (rows2)) <= INT_MAX)) ,
  (CharArray.full row_ptr_2 (Zlength ((Znth i rows1 __default__List_Z))) (Znth i rows1 __default__List_Z) )
|--
  (CharArray.full row_ptr_2 ((string_length ((row_payload_z_74 ((Znth (i) (rows1) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_74 ((Znth (i) (rows1) ((@nil Z))))))) )
.

Definition total_match_entail_wit_3 := 
(
forall (lst2_size_pre: Z) (lst2_pre: Z) (lst1_size_pre: Z) (lst1_pre: Z) (rows2: (@list (@list Z))) (rows1: (@list (@list Z))) (row_ptr: Z) (i: Z) (num2: Z) (len: Z) (num1: Z) (retval: Z) (PreH1 : (retval = (string_length ((row_payload_z_74 ((Znth (i) (rows1) ((@nil Z))))))))) (PreH2 : (0 <= ((string_length ((row_payload_z_74 ((Znth (i) (rows1) ((@nil Z))))))) + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < lst1_size_pre)) (PreH5 : (num2 = 0)) (PreH6 : (0 <= len)) (PreH7 : (len < INT_MAX)) (PreH8 : (rows_well_formed_74 rows1 lst1_size_pre )) (PreH9 : (rows_well_formed_74 rows2 lst2_size_pre )) (PreH10 : (problem_74_pre_z rows1 rows2 )) (PreH11 : (total_prefix_state_74 rows1 i num1 )) (PreH12 : (valid_string (row_payload_z_74 ((Znth (i) (rows1) ((@nil Z))))) )) (PreH13 : ((string_length ((row_payload_z_74 ((Znth (i) (rows1) ((@nil Z))))))) < INT_MAX)) (PreH14 : ((Zlength ((Znth (i) (rows1) ((@nil Z))))) = ((string_length ((row_payload_z_74 ((Znth (i) (rows1) ((@nil Z))))))) + 1 ))) (PreH15 : (0 <= (rows_total_len_z_74 (rows1)))) (PreH16 : ((rows_total_len_z_74 (rows1)) <= INT_MAX)) (PreH17 : (0 <= (rows_total_len_z_74 (rows2)))) (PreH18 : ((rows_total_len_z_74 (rows2)) <= INT_MAX)) ,
  (store_string row_ptr (row_payload_z_74 ((Znth (i) (rows1) ((@nil Z))))) )
  **  (CharPtrArray2.missing_i lst1_pre lst1_size_pre i row_ptr rows1 )
  **  (((lst1_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharPtrArray2.full lst2_pre lst2_size_pre rows2 )
|--
  “ (0 <= i) ” 
  &&  “ (i < lst1_size_pre) ” 
  &&  “ (num2 = 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < INT_MAX) ” 
  &&  “ (rows_well_formed_74 rows1 lst1_size_pre ) ” 
  &&  “ (rows_well_formed_74 rows2 lst2_size_pre ) ” 
  &&  “ (problem_74_pre_z rows1 rows2 ) ” 
  &&  “ (total_prefix_state_74 rows1 (i + 1 ) (num1 + retval ) ) ” 
  &&  “ (0 <= (rows_total_len_z_74 (rows1))) ” 
  &&  “ ((rows_total_len_z_74 (rows1)) <= INT_MAX) ” 
  &&  “ (0 <= (rows_total_len_z_74 (rows2))) ” 
  &&  “ ((rows_total_len_z_74 (rows2)) <= INT_MAX) ”
  &&  (CharPtrArray2.full lst1_pre lst1_size_pre rows1 )
  **  (CharPtrArray2.full lst2_pre lst2_size_pre rows2 )
) \/
(
forall (lst2_size_pre: Z) (lst1_size_pre: Z) (lst1_pre: Z) (rows2: (@list (@list Z))) (rows1: (@list (@list Z))) (row_ptr: Z) (i: Z) (num2: Z) (len: Z) (num1: Z) (retval: Z) (PreH1 : (retval = (string_length ((row_payload_z_74 ((Znth (i) (rows1) ((@nil Z))))))))) (PreH2 : (0 <= ((string_length ((row_payload_z_74 ((Znth (i) (rows1) ((@nil Z))))))) + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < lst1_size_pre)) (PreH5 : (num2 = 0)) (PreH6 : (0 <= len)) (PreH7 : (len < INT_MAX)) (PreH8 : (rows_well_formed_74 rows1 lst1_size_pre )) (PreH9 : (rows_well_formed_74 rows2 lst2_size_pre )) (PreH10 : (problem_74_pre_z rows1 rows2 )) (PreH11 : (total_prefix_state_74 rows1 i num1 )) (PreH12 : (valid_string (row_payload_z_74 ((Znth (i) (rows1) ((@nil Z))))) )) (PreH13 : ((string_length ((row_payload_z_74 ((Znth (i) (rows1) ((@nil Z))))))) < INT_MAX)) (PreH14 : ((Zlength ((Znth (i) (rows1) ((@nil Z))))) = ((string_length ((row_payload_z_74 ((Znth (i) (rows1) ((@nil Z))))))) + 1 ))) (PreH15 : (0 <= (rows_total_len_z_74 (rows1)))) (PreH16 : ((rows_total_len_z_74 (rows1)) <= INT_MAX)) (PreH17 : (0 <= (rows_total_len_z_74 (rows2)))) (PreH18 : ((rows_total_len_z_74 (rows2)) <= INT_MAX)) ,
  (CharArray.full row_ptr ((string_length ((row_payload_z_74 ((Znth (i) (rows1) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_74 ((Znth (i) (rows1) ((@nil Z))))))) )
  **  (CharPtrArray2.missing_i lst1_pre lst1_size_pre i row_ptr rows1 )
  **  (((lst1_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ (total_prefix_state_74 rows1 (i + 1 ) (num1 + retval ) ) ” 
  &&  “ (0 <= retval) ”
  &&  (CharPtrArray2.full lst1_pre lst1_size_pre rows1 )
).

Definition total_match_entail_wit_3_split_goal_1 := 
forall (lst2_size_pre: Z) (lst1_size_pre: Z) (lst1_pre: Z) (rows2: (@list (@list Z))) (rows1: (@list (@list Z))) (row_ptr: Z) (i: Z) (num2: Z) (len: Z) (num1: Z) (retval: Z) (PreH1 : (retval = (string_length ((row_payload_z_74 ((Znth (i) (rows1) ((@nil Z))))))))) (PreH2 : (0 <= ((string_length ((row_payload_z_74 ((Znth (i) (rows1) ((@nil Z))))))) + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < lst1_size_pre)) (PreH5 : (num2 = 0)) (PreH6 : (0 <= len)) (PreH7 : (len < INT_MAX)) (PreH8 : (rows_well_formed_74 rows1 lst1_size_pre )) (PreH9 : (rows_well_formed_74 rows2 lst2_size_pre )) (PreH10 : (problem_74_pre_z rows1 rows2 )) (PreH11 : (total_prefix_state_74 rows1 i num1 )) (PreH12 : (valid_string (row_payload_z_74 ((Znth (i) (rows1) ((@nil Z))))) )) (PreH13 : ((string_length ((row_payload_z_74 ((Znth (i) (rows1) ((@nil Z))))))) < INT_MAX)) (PreH14 : ((Zlength ((Znth (i) (rows1) ((@nil Z))))) = ((string_length ((row_payload_z_74 ((Znth (i) (rows1) ((@nil Z))))))) + 1 ))) (PreH15 : (0 <= (rows_total_len_z_74 (rows1)))) (PreH16 : ((rows_total_len_z_74 (rows1)) <= INT_MAX)) (PreH17 : (0 <= (rows_total_len_z_74 (rows2)))) (PreH18 : ((rows_total_len_z_74 (rows2)) <= INT_MAX)) ,
  (CharArray.full row_ptr ((string_length ((row_payload_z_74 ((Znth (i) (rows1) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_74 ((Znth (i) (rows1) ((@nil Z))))))) )
  **  (CharPtrArray2.missing_i lst1_pre lst1_size_pre i row_ptr rows1 )
  **  (((lst1_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ (total_prefix_state_74 rows1 (i + 1 ) (num1 + retval ) ) ”
.

Definition total_match_entail_wit_3_split_goal_2 := 
forall (lst2_size_pre: Z) (lst1_size_pre: Z) (lst1_pre: Z) (rows2: (@list (@list Z))) (rows1: (@list (@list Z))) (row_ptr: Z) (i: Z) (num2: Z) (len: Z) (num1: Z) (retval: Z) (PreH1 : (retval = (string_length ((row_payload_z_74 ((Znth (i) (rows1) ((@nil Z))))))))) (PreH2 : (0 <= ((string_length ((row_payload_z_74 ((Znth (i) (rows1) ((@nil Z))))))) + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < lst1_size_pre)) (PreH5 : (num2 = 0)) (PreH6 : (0 <= len)) (PreH7 : (len < INT_MAX)) (PreH8 : (rows_well_formed_74 rows1 lst1_size_pre )) (PreH9 : (rows_well_formed_74 rows2 lst2_size_pre )) (PreH10 : (problem_74_pre_z rows1 rows2 )) (PreH11 : (total_prefix_state_74 rows1 i num1 )) (PreH12 : (valid_string (row_payload_z_74 ((Znth (i) (rows1) ((@nil Z))))) )) (PreH13 : ((string_length ((row_payload_z_74 ((Znth (i) (rows1) ((@nil Z))))))) < INT_MAX)) (PreH14 : ((Zlength ((Znth (i) (rows1) ((@nil Z))))) = ((string_length ((row_payload_z_74 ((Znth (i) (rows1) ((@nil Z))))))) + 1 ))) (PreH15 : (0 <= (rows_total_len_z_74 (rows1)))) (PreH16 : ((rows_total_len_z_74 (rows1)) <= INT_MAX)) (PreH17 : (0 <= (rows_total_len_z_74 (rows2)))) (PreH18 : ((rows_total_len_z_74 (rows2)) <= INT_MAX)) ,
  (CharArray.full row_ptr ((string_length ((row_payload_z_74 ((Znth (i) (rows1) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_74 ((Znth (i) (rows1) ((@nil Z))))))) )
  **  (CharPtrArray2.missing_i lst1_pre lst1_size_pre i row_ptr rows1 )
  **  (((lst1_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ (0 <= retval) ”
.

Definition total_match_entail_wit_3_split_goal_spatial := 
forall (lst2_size_pre: Z) (lst1_size_pre: Z) (lst1_pre: Z) (rows2: (@list (@list Z))) (rows1: (@list (@list Z))) (row_ptr: Z) (i: Z) (num2: Z) (len: Z) (num1: Z) (retval: Z) (PreH1 : (retval = (string_length ((row_payload_z_74 ((Znth (i) (rows1) ((@nil Z))))))))) (PreH2 : (0 <= ((string_length ((row_payload_z_74 ((Znth (i) (rows1) ((@nil Z))))))) + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < lst1_size_pre)) (PreH5 : (num2 = 0)) (PreH6 : (0 <= len)) (PreH7 : (len < INT_MAX)) (PreH8 : (rows_well_formed_74 rows1 lst1_size_pre )) (PreH9 : (rows_well_formed_74 rows2 lst2_size_pre )) (PreH10 : (problem_74_pre_z rows1 rows2 )) (PreH11 : (total_prefix_state_74 rows1 i num1 )) (PreH12 : (valid_string (row_payload_z_74 ((Znth (i) (rows1) ((@nil Z))))) )) (PreH13 : ((string_length ((row_payload_z_74 ((Znth (i) (rows1) ((@nil Z))))))) < INT_MAX)) (PreH14 : ((Zlength ((Znth (i) (rows1) ((@nil Z))))) = ((string_length ((row_payload_z_74 ((Znth (i) (rows1) ((@nil Z))))))) + 1 ))) (PreH15 : (0 <= (rows_total_len_z_74 (rows1)))) (PreH16 : ((rows_total_len_z_74 (rows1)) <= INT_MAX)) (PreH17 : (0 <= (rows_total_len_z_74 (rows2)))) (PreH18 : ((rows_total_len_z_74 (rows2)) <= INT_MAX)) ,
  (CharArray.full row_ptr ((string_length ((row_payload_z_74 ((Znth (i) (rows1) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_74 ((Znth (i) (rows1) ((@nil Z))))))) )
  **  (CharPtrArray2.missing_i lst1_pre lst1_size_pre i row_ptr rows1 )
  **  (((lst1_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  (CharPtrArray2.full lst1_pre lst1_size_pre rows1 )
.

Definition total_match_entail_wit_4 := 
forall (lst2_size_pre: Z) (lst2_pre: Z) (lst1_size_pre: Z) (lst1_pre: Z) (rows2: (@list (@list Z))) (rows1: (@list (@list Z))) (i: Z) (num2: Z) (len: Z) (num1: Z) (PreH1 : (0 <= i)) (PreH2 : (i < lst1_size_pre)) (PreH3 : (num2 = 0)) (PreH4 : (0 <= len)) (PreH5 : (len < INT_MAX)) (PreH6 : (rows_well_formed_74 rows1 lst1_size_pre )) (PreH7 : (rows_well_formed_74 rows2 lst2_size_pre )) (PreH8 : (problem_74_pre_z rows1 rows2 )) (PreH9 : (total_prefix_state_74 rows1 (i + 1 ) num1 )) (PreH10 : (0 <= (rows_total_len_z_74 (rows1)))) (PreH11 : ((rows_total_len_z_74 (rows1)) <= INT_MAX)) (PreH12 : (0 <= (rows_total_len_z_74 (rows2)))) (PreH13 : ((rows_total_len_z_74 (rows2)) <= INT_MAX)) ,
  (CharPtrArray2.full lst1_pre lst1_size_pre rows1 )
  **  (CharPtrArray2.full lst2_pre lst2_size_pre rows2 )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= lst1_size_pre) ” 
  &&  “ (num2 = 0) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (rows_well_formed_74 rows1 lst1_size_pre ) ” 
  &&  “ (rows_well_formed_74 rows2 lst2_size_pre ) ” 
  &&  “ (problem_74_pre_z rows1 rows2 ) ” 
  &&  “ (total_prefix_state_74 rows1 (i + 1 ) num1 ) ” 
  &&  “ (0 <= (rows_total_len_z_74 (rows1))) ” 
  &&  “ ((rows_total_len_z_74 (rows1)) <= INT_MAX) ” 
  &&  “ (0 <= (rows_total_len_z_74 (rows2))) ” 
  &&  “ ((rows_total_len_z_74 (rows2)) <= INT_MAX) ”
  &&  (CharPtrArray2.full lst1_pre lst1_size_pre rows1 )
  **  (CharPtrArray2.full lst2_pre lst2_size_pre rows2 )
.

Definition total_match_entail_wit_5 := 
(
forall (lst2_size_pre: Z) (lst2_pre: Z) (lst1_size_pre: Z) (lst1_pre: Z) (rows2: (@list (@list Z))) (rows1: (@list (@list Z))) (num1: Z) (len: Z) (num2: Z) (i: Z) (PreH1 : (i >= lst1_size_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= lst1_size_pre)) (PreH4 : (num2 = 0)) (PreH5 : (0 <= len)) (PreH6 : (len < INT_MAX)) (PreH7 : (rows_well_formed_74 rows1 lst1_size_pre )) (PreH8 : (rows_well_formed_74 rows2 lst2_size_pre )) (PreH9 : (problem_74_pre_z rows1 rows2 )) (PreH10 : (total_prefix_state_74 rows1 i num1 )) (PreH11 : (0 <= (rows_total_len_z_74 (rows1)))) (PreH12 : ((rows_total_len_z_74 (rows1)) <= INT_MAX)) (PreH13 : (0 <= (rows_total_len_z_74 (rows2)))) (PreH14 : ((rows_total_len_z_74 (rows2)) <= INT_MAX)) ,
  (CharPtrArray2.full lst1_pre lst1_size_pre rows1 )
  **  (CharPtrArray2.full lst2_pre lst2_size_pre rows2 )
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= lst2_size_pre) ” 
  &&  “ (num1 = (rows_total_len_z_74 (rows1))) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (rows_well_formed_74 rows1 lst1_size_pre ) ” 
  &&  “ (rows_well_formed_74 rows2 lst2_size_pre ) ” 
  &&  “ (problem_74_pre_z rows1 rows2 ) ” 
  &&  “ (total_prefix_state_74 rows2 0 num2 ) ” 
  &&  “ (0 <= (rows_total_len_z_74 (rows1))) ” 
  &&  “ ((rows_total_len_z_74 (rows1)) <= INT_MAX) ” 
  &&  “ (0 <= (rows_total_len_z_74 (rows2))) ” 
  &&  “ ((rows_total_len_z_74 (rows2)) <= INT_MAX) ”
  &&  (CharPtrArray2.full lst1_pre lst1_size_pre rows1 )
  **  (CharPtrArray2.full lst2_pre lst2_size_pre rows2 )
) \/
(
forall (lst2_size_pre: Z) (lst1_size_pre: Z) (rows2: (@list (@list Z))) (rows1: (@list (@list Z))) (num1: Z) (len: Z) (num2: Z) (i: Z) (PreH1 : (i >= lst1_size_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= lst1_size_pre)) (PreH4 : (num2 = 0)) (PreH5 : (0 <= len)) (PreH6 : (len < INT_MAX)) (PreH7 : (rows_well_formed_74 rows1 lst1_size_pre )) (PreH8 : (rows_well_formed_74 rows2 lst2_size_pre )) (PreH9 : (problem_74_pre_z rows1 rows2 )) (PreH10 : (total_prefix_state_74 rows1 i num1 )) (PreH11 : (0 <= (rows_total_len_z_74 (rows1)))) (PreH12 : ((rows_total_len_z_74 (rows1)) <= INT_MAX)) (PreH13 : (0 <= (rows_total_len_z_74 (rows2)))) (PreH14 : ((rows_total_len_z_74 (rows2)) <= INT_MAX)) ,
  TT && emp 
|--
  “ (total_prefix_state_74 rows2 0 num2 ) ” 
  &&  “ (num1 = (rows_total_len_z_74 (rows1))) ” 
  &&  “ (0 <= lst2_size_pre) ”
  &&  emp
).

Definition total_match_entail_wit_5_split_goal_1 := 
forall (lst2_size_pre: Z) (lst1_size_pre: Z) (rows2: (@list (@list Z))) (rows1: (@list (@list Z))) (num1: Z) (len: Z) (num2: Z) (i: Z) (PreH1 : (i >= lst1_size_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= lst1_size_pre)) (PreH4 : (num2 = 0)) (PreH5 : (0 <= len)) (PreH6 : (len < INT_MAX)) (PreH7 : (rows_well_formed_74 rows1 lst1_size_pre )) (PreH8 : (rows_well_formed_74 rows2 lst2_size_pre )) (PreH9 : (problem_74_pre_z rows1 rows2 )) (PreH10 : (total_prefix_state_74 rows1 i num1 )) (PreH11 : (0 <= (rows_total_len_z_74 (rows1)))) (PreH12 : ((rows_total_len_z_74 (rows1)) <= INT_MAX)) (PreH13 : (0 <= (rows_total_len_z_74 (rows2)))) (PreH14 : ((rows_total_len_z_74 (rows2)) <= INT_MAX)) ,
  TT && emp 
|--
  “ (total_prefix_state_74 rows2 0 num2 ) ”
.

Definition total_match_entail_wit_5_split_goal_2 := 
forall (lst2_size_pre: Z) (lst1_size_pre: Z) (rows2: (@list (@list Z))) (rows1: (@list (@list Z))) (num1: Z) (len: Z) (num2: Z) (i: Z) (PreH1 : (i >= lst1_size_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= lst1_size_pre)) (PreH4 : (num2 = 0)) (PreH5 : (0 <= len)) (PreH6 : (len < INT_MAX)) (PreH7 : (rows_well_formed_74 rows1 lst1_size_pre )) (PreH8 : (rows_well_formed_74 rows2 lst2_size_pre )) (PreH9 : (problem_74_pre_z rows1 rows2 )) (PreH10 : (total_prefix_state_74 rows1 i num1 )) (PreH11 : (0 <= (rows_total_len_z_74 (rows1)))) (PreH12 : ((rows_total_len_z_74 (rows1)) <= INT_MAX)) (PreH13 : (0 <= (rows_total_len_z_74 (rows2)))) (PreH14 : ((rows_total_len_z_74 (rows2)) <= INT_MAX)) ,
  TT && emp 
|--
  “ (num1 = (rows_total_len_z_74 (rows1))) ”
.

Definition total_match_entail_wit_5_split_goal_3 := 
forall (lst2_size_pre: Z) (lst1_size_pre: Z) (rows2: (@list (@list Z))) (rows1: (@list (@list Z))) (num1: Z) (len: Z) (num2: Z) (i: Z) (PreH1 : (i >= lst1_size_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= lst1_size_pre)) (PreH4 : (num2 = 0)) (PreH5 : (0 <= len)) (PreH6 : (len < INT_MAX)) (PreH7 : (rows_well_formed_74 rows1 lst1_size_pre )) (PreH8 : (rows_well_formed_74 rows2 lst2_size_pre )) (PreH9 : (problem_74_pre_z rows1 rows2 )) (PreH10 : (total_prefix_state_74 rows1 i num1 )) (PreH11 : (0 <= (rows_total_len_z_74 (rows1)))) (PreH12 : ((rows_total_len_z_74 (rows1)) <= INT_MAX)) (PreH13 : (0 <= (rows_total_len_z_74 (rows2)))) (PreH14 : ((rows_total_len_z_74 (rows2)) <= INT_MAX)) ,
  TT && emp 
|--
  “ (0 <= lst2_size_pre) ”
.

Definition total_match_entail_wit_6 := 
(
forall (lst2_size_pre: Z) (lst2_pre: Z) (lst1_size_pre: Z) (lst1_pre: Z) (rows2: (@list (@list Z))) (rows1: (@list (@list Z))) (num2: Z) (len: Z) (num1: Z) (i: Z) (PreH1 : (i < lst2_size_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= lst2_size_pre)) (PreH4 : (num1 = (rows_total_len_z_74 (rows1)))) (PreH5 : (0 <= len)) (PreH6 : (len < INT_MAX)) (PreH7 : (rows_well_formed_74 rows1 lst1_size_pre )) (PreH8 : (rows_well_formed_74 rows2 lst2_size_pre )) (PreH9 : (problem_74_pre_z rows1 rows2 )) (PreH10 : (total_prefix_state_74 rows2 i num2 )) (PreH11 : (0 <= (rows_total_len_z_74 (rows1)))) (PreH12 : ((rows_total_len_z_74 (rows1)) <= INT_MAX)) (PreH13 : (0 <= (rows_total_len_z_74 (rows2)))) (PreH14 : ((rows_total_len_z_74 (rows2)) <= INT_MAX)) ,
  (CharPtrArray2.full lst1_pre lst1_size_pre rows1 )
  **  (CharPtrArray2.full lst2_pre lst2_size_pre rows2 )
|--
  EX (row_ptr: Z) ,
  “ (0 <= i) ” 
  &&  “ (i < lst2_size_pre) ” 
  &&  “ (num1 = (rows_total_len_z_74 (rows1))) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (rows_well_formed_74 rows1 lst1_size_pre ) ” 
  &&  “ (rows_well_formed_74 rows2 lst2_size_pre ) ” 
  &&  “ (problem_74_pre_z rows1 rows2 ) ” 
  &&  “ (total_prefix_state_74 rows2 i num2 ) ” 
  &&  “ (valid_string (row_payload_z_74 ((Znth (i) (rows2) ((@nil Z))))) ) ” 
  &&  “ ((string_length ((row_payload_z_74 ((Znth (i) (rows2) ((@nil Z))))))) < INT_MAX) ” 
  &&  “ ((Zlength ((Znth (i) (rows2) ((@nil Z))))) = ((string_length ((row_payload_z_74 ((Znth (i) (rows2) ((@nil Z))))))) + 1 )) ” 
  &&  “ (0 <= (rows_total_len_z_74 (rows1))) ” 
  &&  “ ((rows_total_len_z_74 (rows1)) <= INT_MAX) ” 
  &&  “ (0 <= (rows_total_len_z_74 (rows2))) ” 
  &&  “ ((rows_total_len_z_74 (rows2)) <= INT_MAX) ”
  &&  (CharPtrArray2.full lst1_pre lst1_size_pre rows1 )
  **  (CharPtrArray2.missing_i lst2_pre lst2_size_pre i row_ptr rows2 )
  **  (((lst2_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_74 ((Znth (i) (rows2) ((@nil Z))))) )
) \/
(
forall (lst2_size_pre: Z) (lst1_size_pre: Z) (rows2: (@list (@list Z))) (rows1: (@list (@list Z))) (num2: Z) (len: Z) (num1: Z) (i: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (0 <= (Zlength ((Znth i rows2 __default__List_Z))))) (PreH2 : (i < lst2_size_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= lst2_size_pre)) (PreH5 : (num1 = (rows_total_len_z_74 (rows1)))) (PreH6 : (0 <= len)) (PreH7 : (len < INT_MAX)) (PreH8 : (rows_well_formed_74 rows1 lst1_size_pre )) (PreH9 : (rows_well_formed_74 rows2 lst2_size_pre )) (PreH10 : (problem_74_pre_z rows1 rows2 )) (PreH11 : (total_prefix_state_74 rows2 i num2 )) (PreH12 : (0 <= (rows_total_len_z_74 (rows1)))) (PreH13 : ((rows_total_len_z_74 (rows1)) <= INT_MAX)) (PreH14 : (0 <= (rows_total_len_z_74 (rows2)))) (PreH15 : ((rows_total_len_z_74 (rows2)) <= INT_MAX)) ,
  (CharArray.full row_ptr_2 (Zlength ((Znth i rows2 __default__List_Z))) (Znth i rows2 __default__List_Z) )
|--
  “ ((Zlength ((Znth (i) (rows2) ((@nil Z))))) = ((string_length ((row_payload_z_74 ((Znth (i) (rows2) ((@nil Z))))))) + 1 )) ” 
  &&  “ ((string_length ((row_payload_z_74 ((Znth (i) (rows2) ((@nil Z))))))) < INT_MAX) ” 
  &&  “ (valid_string (row_payload_z_74 ((Znth (i) (rows2) ((@nil Z))))) ) ”
  &&  (CharArray.full row_ptr_2 ((string_length ((row_payload_z_74 ((Znth (i) (rows2) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_74 ((Znth (i) (rows2) ((@nil Z))))))) )
).

Definition total_match_entail_wit_6_split_goal_1 := 
forall (lst2_size_pre: Z) (lst1_size_pre: Z) (rows2: (@list (@list Z))) (rows1: (@list (@list Z))) (num2: Z) (len: Z) (num1: Z) (i: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (0 <= (Zlength ((Znth i rows2 __default__List_Z))))) (PreH2 : (i < lst2_size_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= lst2_size_pre)) (PreH5 : (num1 = (rows_total_len_z_74 (rows1)))) (PreH6 : (0 <= len)) (PreH7 : (len < INT_MAX)) (PreH8 : (rows_well_formed_74 rows1 lst1_size_pre )) (PreH9 : (rows_well_formed_74 rows2 lst2_size_pre )) (PreH10 : (problem_74_pre_z rows1 rows2 )) (PreH11 : (total_prefix_state_74 rows2 i num2 )) (PreH12 : (0 <= (rows_total_len_z_74 (rows1)))) (PreH13 : ((rows_total_len_z_74 (rows1)) <= INT_MAX)) (PreH14 : (0 <= (rows_total_len_z_74 (rows2)))) (PreH15 : ((rows_total_len_z_74 (rows2)) <= INT_MAX)) ,
  (CharArray.full row_ptr_2 (Zlength ((Znth i rows2 __default__List_Z))) (Znth i rows2 __default__List_Z) )
|--
  “ ((Zlength ((Znth (i) (rows2) ((@nil Z))))) = ((string_length ((row_payload_z_74 ((Znth (i) (rows2) ((@nil Z))))))) + 1 )) ”
.

Definition total_match_entail_wit_6_split_goal_2 := 
forall (lst2_size_pre: Z) (lst1_size_pre: Z) (rows2: (@list (@list Z))) (rows1: (@list (@list Z))) (num2: Z) (len: Z) (num1: Z) (i: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (0 <= (Zlength ((Znth i rows2 __default__List_Z))))) (PreH2 : (i < lst2_size_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= lst2_size_pre)) (PreH5 : (num1 = (rows_total_len_z_74 (rows1)))) (PreH6 : (0 <= len)) (PreH7 : (len < INT_MAX)) (PreH8 : (rows_well_formed_74 rows1 lst1_size_pre )) (PreH9 : (rows_well_formed_74 rows2 lst2_size_pre )) (PreH10 : (problem_74_pre_z rows1 rows2 )) (PreH11 : (total_prefix_state_74 rows2 i num2 )) (PreH12 : (0 <= (rows_total_len_z_74 (rows1)))) (PreH13 : ((rows_total_len_z_74 (rows1)) <= INT_MAX)) (PreH14 : (0 <= (rows_total_len_z_74 (rows2)))) (PreH15 : ((rows_total_len_z_74 (rows2)) <= INT_MAX)) ,
  (CharArray.full row_ptr_2 (Zlength ((Znth i rows2 __default__List_Z))) (Znth i rows2 __default__List_Z) )
|--
  “ ((string_length ((row_payload_z_74 ((Znth (i) (rows2) ((@nil Z))))))) < INT_MAX) ”
.

Definition total_match_entail_wit_6_split_goal_3 := 
forall (lst2_size_pre: Z) (lst1_size_pre: Z) (rows2: (@list (@list Z))) (rows1: (@list (@list Z))) (num2: Z) (len: Z) (num1: Z) (i: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (0 <= (Zlength ((Znth i rows2 __default__List_Z))))) (PreH2 : (i < lst2_size_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= lst2_size_pre)) (PreH5 : (num1 = (rows_total_len_z_74 (rows1)))) (PreH6 : (0 <= len)) (PreH7 : (len < INT_MAX)) (PreH8 : (rows_well_formed_74 rows1 lst1_size_pre )) (PreH9 : (rows_well_formed_74 rows2 lst2_size_pre )) (PreH10 : (problem_74_pre_z rows1 rows2 )) (PreH11 : (total_prefix_state_74 rows2 i num2 )) (PreH12 : (0 <= (rows_total_len_z_74 (rows1)))) (PreH13 : ((rows_total_len_z_74 (rows1)) <= INT_MAX)) (PreH14 : (0 <= (rows_total_len_z_74 (rows2)))) (PreH15 : ((rows_total_len_z_74 (rows2)) <= INT_MAX)) ,
  (CharArray.full row_ptr_2 (Zlength ((Znth i rows2 __default__List_Z))) (Znth i rows2 __default__List_Z) )
|--
  “ (valid_string (row_payload_z_74 ((Znth (i) (rows2) ((@nil Z))))) ) ”
.

Definition total_match_entail_wit_6_split_goal_spatial := 
forall (lst2_size_pre: Z) (lst1_size_pre: Z) (rows2: (@list (@list Z))) (rows1: (@list (@list Z))) (num2: Z) (len: Z) (num1: Z) (i: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (0 <= (Zlength ((Znth i rows2 __default__List_Z))))) (PreH2 : (i < lst2_size_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= lst2_size_pre)) (PreH5 : (num1 = (rows_total_len_z_74 (rows1)))) (PreH6 : (0 <= len)) (PreH7 : (len < INT_MAX)) (PreH8 : (rows_well_formed_74 rows1 lst1_size_pre )) (PreH9 : (rows_well_formed_74 rows2 lst2_size_pre )) (PreH10 : (problem_74_pre_z rows1 rows2 )) (PreH11 : (total_prefix_state_74 rows2 i num2 )) (PreH12 : (0 <= (rows_total_len_z_74 (rows1)))) (PreH13 : ((rows_total_len_z_74 (rows1)) <= INT_MAX)) (PreH14 : (0 <= (rows_total_len_z_74 (rows2)))) (PreH15 : ((rows_total_len_z_74 (rows2)) <= INT_MAX)) ,
  (CharArray.full row_ptr_2 (Zlength ((Znth i rows2 __default__List_Z))) (Znth i rows2 __default__List_Z) )
|--
  (CharArray.full row_ptr_2 ((string_length ((row_payload_z_74 ((Znth (i) (rows2) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_74 ((Znth (i) (rows2) ((@nil Z))))))) )
.

Definition total_match_entail_wit_7 := 
(
forall (lst2_size_pre: Z) (lst2_pre: Z) (lst1_size_pre: Z) (lst1_pre: Z) (rows2: (@list (@list Z))) (rows1: (@list (@list Z))) (row_ptr: Z) (i: Z) (num1: Z) (len: Z) (num2: Z) (retval: Z) (PreH1 : (retval = (string_length ((row_payload_z_74 ((Znth (i) (rows2) ((@nil Z))))))))) (PreH2 : (0 <= ((string_length ((row_payload_z_74 ((Znth (i) (rows2) ((@nil Z))))))) + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < lst2_size_pre)) (PreH5 : (num1 = (rows_total_len_z_74 (rows1)))) (PreH6 : (0 <= len)) (PreH7 : (len < INT_MAX)) (PreH8 : (rows_well_formed_74 rows1 lst1_size_pre )) (PreH9 : (rows_well_formed_74 rows2 lst2_size_pre )) (PreH10 : (problem_74_pre_z rows1 rows2 )) (PreH11 : (total_prefix_state_74 rows2 i num2 )) (PreH12 : (valid_string (row_payload_z_74 ((Znth (i) (rows2) ((@nil Z))))) )) (PreH13 : ((string_length ((row_payload_z_74 ((Znth (i) (rows2) ((@nil Z))))))) < INT_MAX)) (PreH14 : ((Zlength ((Znth (i) (rows2) ((@nil Z))))) = ((string_length ((row_payload_z_74 ((Znth (i) (rows2) ((@nil Z))))))) + 1 ))) (PreH15 : (0 <= (rows_total_len_z_74 (rows1)))) (PreH16 : ((rows_total_len_z_74 (rows1)) <= INT_MAX)) (PreH17 : (0 <= (rows_total_len_z_74 (rows2)))) (PreH18 : ((rows_total_len_z_74 (rows2)) <= INT_MAX)) ,
  (store_string row_ptr (row_payload_z_74 ((Znth (i) (rows2) ((@nil Z))))) )
  **  (CharPtrArray2.full lst1_pre lst1_size_pre rows1 )
  **  (CharPtrArray2.missing_i lst2_pre lst2_size_pre i row_ptr rows2 )
  **  (((lst2_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ (0 <= i) ” 
  &&  “ (i < lst2_size_pre) ” 
  &&  “ (num1 = (rows_total_len_z_74 (rows1))) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < INT_MAX) ” 
  &&  “ (rows_well_formed_74 rows1 lst1_size_pre ) ” 
  &&  “ (rows_well_formed_74 rows2 lst2_size_pre ) ” 
  &&  “ (problem_74_pre_z rows1 rows2 ) ” 
  &&  “ (total_prefix_state_74 rows2 (i + 1 ) (num2 + retval ) ) ” 
  &&  “ (0 <= (rows_total_len_z_74 (rows1))) ” 
  &&  “ ((rows_total_len_z_74 (rows1)) <= INT_MAX) ” 
  &&  “ (0 <= (rows_total_len_z_74 (rows2))) ” 
  &&  “ ((rows_total_len_z_74 (rows2)) <= INT_MAX) ”
  &&  (CharPtrArray2.full lst1_pre lst1_size_pre rows1 )
  **  (CharPtrArray2.full lst2_pre lst2_size_pre rows2 )
) \/
(
forall (lst2_size_pre: Z) (lst2_pre: Z) (lst1_size_pre: Z) (rows2: (@list (@list Z))) (rows1: (@list (@list Z))) (row_ptr: Z) (i: Z) (num1: Z) (len: Z) (num2: Z) (retval: Z) (PreH1 : (retval = (string_length ((row_payload_z_74 ((Znth (i) (rows2) ((@nil Z))))))))) (PreH2 : (0 <= ((string_length ((row_payload_z_74 ((Znth (i) (rows2) ((@nil Z))))))) + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < lst2_size_pre)) (PreH5 : (num1 = (rows_total_len_z_74 (rows1)))) (PreH6 : (0 <= len)) (PreH7 : (len < INT_MAX)) (PreH8 : (rows_well_formed_74 rows1 lst1_size_pre )) (PreH9 : (rows_well_formed_74 rows2 lst2_size_pre )) (PreH10 : (problem_74_pre_z rows1 rows2 )) (PreH11 : (total_prefix_state_74 rows2 i num2 )) (PreH12 : (valid_string (row_payload_z_74 ((Znth (i) (rows2) ((@nil Z))))) )) (PreH13 : ((string_length ((row_payload_z_74 ((Znth (i) (rows2) ((@nil Z))))))) < INT_MAX)) (PreH14 : ((Zlength ((Znth (i) (rows2) ((@nil Z))))) = ((string_length ((row_payload_z_74 ((Znth (i) (rows2) ((@nil Z))))))) + 1 ))) (PreH15 : (0 <= (rows_total_len_z_74 (rows1)))) (PreH16 : ((rows_total_len_z_74 (rows1)) <= INT_MAX)) (PreH17 : (0 <= (rows_total_len_z_74 (rows2)))) (PreH18 : ((rows_total_len_z_74 (rows2)) <= INT_MAX)) ,
  (CharArray.full row_ptr ((string_length ((row_payload_z_74 ((Znth (i) (rows2) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_74 ((Znth (i) (rows2) ((@nil Z))))))) )
  **  (CharPtrArray2.missing_i lst2_pre lst2_size_pre i row_ptr rows2 )
  **  (((lst2_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ (total_prefix_state_74 rows2 (i + 1 ) (num2 + retval ) ) ” 
  &&  “ (0 <= retval) ”
  &&  (CharPtrArray2.full lst2_pre lst2_size_pre rows2 )
).

Definition total_match_entail_wit_7_split_goal_1 := 
forall (lst2_size_pre: Z) (lst2_pre: Z) (lst1_size_pre: Z) (rows2: (@list (@list Z))) (rows1: (@list (@list Z))) (row_ptr: Z) (i: Z) (num1: Z) (len: Z) (num2: Z) (retval: Z) (PreH1 : (retval = (string_length ((row_payload_z_74 ((Znth (i) (rows2) ((@nil Z))))))))) (PreH2 : (0 <= ((string_length ((row_payload_z_74 ((Znth (i) (rows2) ((@nil Z))))))) + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < lst2_size_pre)) (PreH5 : (num1 = (rows_total_len_z_74 (rows1)))) (PreH6 : (0 <= len)) (PreH7 : (len < INT_MAX)) (PreH8 : (rows_well_formed_74 rows1 lst1_size_pre )) (PreH9 : (rows_well_formed_74 rows2 lst2_size_pre )) (PreH10 : (problem_74_pre_z rows1 rows2 )) (PreH11 : (total_prefix_state_74 rows2 i num2 )) (PreH12 : (valid_string (row_payload_z_74 ((Znth (i) (rows2) ((@nil Z))))) )) (PreH13 : ((string_length ((row_payload_z_74 ((Znth (i) (rows2) ((@nil Z))))))) < INT_MAX)) (PreH14 : ((Zlength ((Znth (i) (rows2) ((@nil Z))))) = ((string_length ((row_payload_z_74 ((Znth (i) (rows2) ((@nil Z))))))) + 1 ))) (PreH15 : (0 <= (rows_total_len_z_74 (rows1)))) (PreH16 : ((rows_total_len_z_74 (rows1)) <= INT_MAX)) (PreH17 : (0 <= (rows_total_len_z_74 (rows2)))) (PreH18 : ((rows_total_len_z_74 (rows2)) <= INT_MAX)) ,
  (CharArray.full row_ptr ((string_length ((row_payload_z_74 ((Znth (i) (rows2) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_74 ((Znth (i) (rows2) ((@nil Z))))))) )
  **  (CharPtrArray2.missing_i lst2_pre lst2_size_pre i row_ptr rows2 )
  **  (((lst2_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ (total_prefix_state_74 rows2 (i + 1 ) (num2 + retval ) ) ”
.

Definition total_match_entail_wit_7_split_goal_2 := 
forall (lst2_size_pre: Z) (lst2_pre: Z) (lst1_size_pre: Z) (rows2: (@list (@list Z))) (rows1: (@list (@list Z))) (row_ptr: Z) (i: Z) (num1: Z) (len: Z) (num2: Z) (retval: Z) (PreH1 : (retval = (string_length ((row_payload_z_74 ((Znth (i) (rows2) ((@nil Z))))))))) (PreH2 : (0 <= ((string_length ((row_payload_z_74 ((Znth (i) (rows2) ((@nil Z))))))) + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < lst2_size_pre)) (PreH5 : (num1 = (rows_total_len_z_74 (rows1)))) (PreH6 : (0 <= len)) (PreH7 : (len < INT_MAX)) (PreH8 : (rows_well_formed_74 rows1 lst1_size_pre )) (PreH9 : (rows_well_formed_74 rows2 lst2_size_pre )) (PreH10 : (problem_74_pre_z rows1 rows2 )) (PreH11 : (total_prefix_state_74 rows2 i num2 )) (PreH12 : (valid_string (row_payload_z_74 ((Znth (i) (rows2) ((@nil Z))))) )) (PreH13 : ((string_length ((row_payload_z_74 ((Znth (i) (rows2) ((@nil Z))))))) < INT_MAX)) (PreH14 : ((Zlength ((Znth (i) (rows2) ((@nil Z))))) = ((string_length ((row_payload_z_74 ((Znth (i) (rows2) ((@nil Z))))))) + 1 ))) (PreH15 : (0 <= (rows_total_len_z_74 (rows1)))) (PreH16 : ((rows_total_len_z_74 (rows1)) <= INT_MAX)) (PreH17 : (0 <= (rows_total_len_z_74 (rows2)))) (PreH18 : ((rows_total_len_z_74 (rows2)) <= INT_MAX)) ,
  (CharArray.full row_ptr ((string_length ((row_payload_z_74 ((Znth (i) (rows2) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_74 ((Znth (i) (rows2) ((@nil Z))))))) )
  **  (CharPtrArray2.missing_i lst2_pre lst2_size_pre i row_ptr rows2 )
  **  (((lst2_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ (0 <= retval) ”
.

Definition total_match_entail_wit_7_split_goal_spatial := 
forall (lst2_size_pre: Z) (lst2_pre: Z) (lst1_size_pre: Z) (rows2: (@list (@list Z))) (rows1: (@list (@list Z))) (row_ptr: Z) (i: Z) (num1: Z) (len: Z) (num2: Z) (retval: Z) (PreH1 : (retval = (string_length ((row_payload_z_74 ((Znth (i) (rows2) ((@nil Z))))))))) (PreH2 : (0 <= ((string_length ((row_payload_z_74 ((Znth (i) (rows2) ((@nil Z))))))) + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < lst2_size_pre)) (PreH5 : (num1 = (rows_total_len_z_74 (rows1)))) (PreH6 : (0 <= len)) (PreH7 : (len < INT_MAX)) (PreH8 : (rows_well_formed_74 rows1 lst1_size_pre )) (PreH9 : (rows_well_formed_74 rows2 lst2_size_pre )) (PreH10 : (problem_74_pre_z rows1 rows2 )) (PreH11 : (total_prefix_state_74 rows2 i num2 )) (PreH12 : (valid_string (row_payload_z_74 ((Znth (i) (rows2) ((@nil Z))))) )) (PreH13 : ((string_length ((row_payload_z_74 ((Znth (i) (rows2) ((@nil Z))))))) < INT_MAX)) (PreH14 : ((Zlength ((Znth (i) (rows2) ((@nil Z))))) = ((string_length ((row_payload_z_74 ((Znth (i) (rows2) ((@nil Z))))))) + 1 ))) (PreH15 : (0 <= (rows_total_len_z_74 (rows1)))) (PreH16 : ((rows_total_len_z_74 (rows1)) <= INT_MAX)) (PreH17 : (0 <= (rows_total_len_z_74 (rows2)))) (PreH18 : ((rows_total_len_z_74 (rows2)) <= INT_MAX)) ,
  (CharArray.full row_ptr ((string_length ((row_payload_z_74 ((Znth (i) (rows2) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_74 ((Znth (i) (rows2) ((@nil Z))))))) )
  **  (CharPtrArray2.missing_i lst2_pre lst2_size_pre i row_ptr rows2 )
  **  (((lst2_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  (CharPtrArray2.full lst2_pre lst2_size_pre rows2 )
.

Definition total_match_entail_wit_8 := 
forall (lst2_size_pre: Z) (lst2_pre: Z) (lst1_size_pre: Z) (lst1_pre: Z) (rows2: (@list (@list Z))) (rows1: (@list (@list Z))) (i: Z) (num1: Z) (len: Z) (num2: Z) (PreH1 : (0 <= i)) (PreH2 : (i < lst2_size_pre)) (PreH3 : (num1 = (rows_total_len_z_74 (rows1)))) (PreH4 : (0 <= len)) (PreH5 : (len < INT_MAX)) (PreH6 : (rows_well_formed_74 rows1 lst1_size_pre )) (PreH7 : (rows_well_formed_74 rows2 lst2_size_pre )) (PreH8 : (problem_74_pre_z rows1 rows2 )) (PreH9 : (total_prefix_state_74 rows2 (i + 1 ) num2 )) (PreH10 : (0 <= (rows_total_len_z_74 (rows1)))) (PreH11 : ((rows_total_len_z_74 (rows1)) <= INT_MAX)) (PreH12 : (0 <= (rows_total_len_z_74 (rows2)))) (PreH13 : ((rows_total_len_z_74 (rows2)) <= INT_MAX)) ,
  (CharPtrArray2.full lst1_pre lst1_size_pre rows1 )
  **  (CharPtrArray2.full lst2_pre lst2_size_pre rows2 )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= lst2_size_pre) ” 
  &&  “ (num1 = (rows_total_len_z_74 (rows1))) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (rows_well_formed_74 rows1 lst1_size_pre ) ” 
  &&  “ (rows_well_formed_74 rows2 lst2_size_pre ) ” 
  &&  “ (problem_74_pre_z rows1 rows2 ) ” 
  &&  “ (total_prefix_state_74 rows2 (i + 1 ) num2 ) ” 
  &&  “ (0 <= (rows_total_len_z_74 (rows1))) ” 
  &&  “ ((rows_total_len_z_74 (rows1)) <= INT_MAX) ” 
  &&  “ (0 <= (rows_total_len_z_74 (rows2))) ” 
  &&  “ ((rows_total_len_z_74 (rows2)) <= INT_MAX) ”
  &&  (CharPtrArray2.full lst1_pre lst1_size_pre rows1 )
  **  (CharPtrArray2.full lst2_pre lst2_size_pre rows2 )
.

Definition total_match_return_wit_1 := 
forall (lst2_size_pre: Z) (lst2_pre: Z) (lst1_size_pre: Z) (lst1_pre: Z) (rows2: (@list (@list Z))) (rows1: (@list (@list Z))) (num2: Z) (len: Z) (num1: Z) (i: Z) (retval: Z) (PreH1 : (num1 <= num2)) (PreH2 : (retval <> 0)) (PreH3 : (i >= lst2_size_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= lst2_size_pre)) (PreH6 : (num1 = (rows_total_len_z_74 (rows1)))) (PreH7 : (0 <= len)) (PreH8 : (len < INT_MAX)) (PreH9 : (rows_well_formed_74 rows1 lst1_size_pre )) (PreH10 : (rows_well_formed_74 rows2 lst2_size_pre )) (PreH11 : (problem_74_pre_z rows1 rows2 )) (PreH12 : (total_prefix_state_74 rows2 i num2 )) (PreH13 : (0 <= (rows_total_len_z_74 (rows1)))) (PreH14 : ((rows_total_len_z_74 (rows1)) <= INT_MAX)) (PreH15 : (0 <= (rows_total_len_z_74 (rows2)))) (PreH16 : ((rows_total_len_z_74 (rows2)) <= INT_MAX)) ,
  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> lst1_pre)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst1_size_pre)
  **  (CharPtrArray2.full lst1_pre lst1_size_pre rows1 )
  **  (CharPtrArray2.full lst2_pre lst2_size_pre rows2 )
|--
  (EX (data: Z)  (output_rows: (@list (@list Z)))  (output_size: Z) ,
  “ (retval <> 0) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= 100) ” 
  &&  “ (problem_74_spec_z rows1 rows2 output_rows ) ” 
  &&  “ (data = lst1_pre) ” 
  &&  “ (output_size = lst1_size_pre) ” 
  &&  “ (output_rows = rows1) ”
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (CharPtrArray2.full lst1_pre lst1_size_pre rows1 )
  **  (CharPtrArray2.full lst2_pre lst2_size_pre rows2 ))
  ||
  (EX (data: Z)  (output_rows: (@list (@list Z)))  (output_size: Z) ,
  “ (retval <> 0) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= 100) ” 
  &&  “ (problem_74_spec_z rows1 rows2 output_rows ) ” 
  &&  “ (data = lst2_pre) ” 
  &&  “ (output_size = lst2_size_pre) ” 
  &&  “ (output_rows = rows2) ”
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (CharPtrArray2.full lst1_pre lst1_size_pre rows1 )
  **  (CharPtrArray2.full lst2_pre lst2_size_pre rows2 ))
.

Definition total_match_return_wit_2 := 
forall (lst2_size_pre: Z) (lst2_pre: Z) (lst1_size_pre: Z) (lst1_pre: Z) (rows2: (@list (@list Z))) (rows1: (@list (@list Z))) (num2: Z) (len: Z) (num1: Z) (i: Z) (retval: Z) (PreH1 : (num1 > num2)) (PreH2 : (retval <> 0)) (PreH3 : (i >= lst2_size_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= lst2_size_pre)) (PreH6 : (num1 = (rows_total_len_z_74 (rows1)))) (PreH7 : (0 <= len)) (PreH8 : (len < INT_MAX)) (PreH9 : (rows_well_formed_74 rows1 lst1_size_pre )) (PreH10 : (rows_well_formed_74 rows2 lst2_size_pre )) (PreH11 : (problem_74_pre_z rows1 rows2 )) (PreH12 : (total_prefix_state_74 rows2 i num2 )) (PreH13 : (0 <= (rows_total_len_z_74 (rows1)))) (PreH14 : ((rows_total_len_z_74 (rows1)) <= INT_MAX)) (PreH15 : (0 <= (rows_total_len_z_74 (rows2)))) (PreH16 : ((rows_total_len_z_74 (rows2)) <= INT_MAX)) ,
  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> lst2_pre)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst2_size_pre)
  **  (CharPtrArray2.full lst1_pre lst1_size_pre rows1 )
  **  (CharPtrArray2.full lst2_pre lst2_size_pre rows2 )
|--
  (EX (data: Z)  (output_rows: (@list (@list Z)))  (output_size: Z) ,
  “ (retval <> 0) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= 100) ” 
  &&  “ (problem_74_spec_z rows1 rows2 output_rows ) ” 
  &&  “ (data = lst1_pre) ” 
  &&  “ (output_size = lst1_size_pre) ” 
  &&  “ (output_rows = rows1) ”
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (CharPtrArray2.full lst1_pre lst1_size_pre rows1 )
  **  (CharPtrArray2.full lst2_pre lst2_size_pre rows2 ))
  ||
  (EX (data: Z)  (output_rows: (@list (@list Z)))  (output_size: Z) ,
  “ (retval <> 0) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= 100) ” 
  &&  “ (problem_74_spec_z rows1 rows2 output_rows ) ” 
  &&  “ (data = lst2_pre) ” 
  &&  “ (output_size = lst2_size_pre) ” 
  &&  “ (output_rows = rows2) ”
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (CharPtrArray2.full lst1_pre lst1_size_pre rows1 )
  **  (CharPtrArray2.full lst2_pre lst2_size_pre rows2 ))
.

Definition total_match_partial_solve_wit_1_pure := 
forall (lst2_size_pre: Z) (lst2_pre: Z) (lst1_size_pre: Z) (lst1_pre: Z) (rows2: (@list (@list Z))) (rows1: (@list (@list Z))) (row_ptr: Z) (i: Z) (num2: Z) (len: Z) (num1: Z) (PreH1 : (0 <= i)) (PreH2 : (i < lst1_size_pre)) (PreH3 : (num2 = 0)) (PreH4 : (0 <= len)) (PreH5 : (len < INT_MAX)) (PreH6 : (rows_well_formed_74 rows1 lst1_size_pre )) (PreH7 : (rows_well_formed_74 rows2 lst2_size_pre )) (PreH8 : (problem_74_pre_z rows1 rows2 )) (PreH9 : (total_prefix_state_74 rows1 i num1 )) (PreH10 : (valid_string (row_payload_z_74 ((Znth (i) (rows1) ((@nil Z))))) )) (PreH11 : ((string_length ((row_payload_z_74 ((Znth (i) (rows1) ((@nil Z))))))) < INT_MAX)) (PreH12 : ((Zlength ((Znth (i) (rows1) ((@nil Z))))) = ((string_length ((row_payload_z_74 ((Znth (i) (rows1) ((@nil Z))))))) + 1 ))) (PreH13 : (0 <= (rows_total_len_z_74 (rows1)))) (PreH14 : ((rows_total_len_z_74 (rows1)) <= INT_MAX)) (PreH15 : (0 <= (rows_total_len_z_74 (rows2)))) (PreH16 : ((rows_total_len_z_74 (rows2)) <= INT_MAX)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lst1_size" ) )) # Int  |-> lst1_size_pre)
  **  ((( &( "lst2_size" ) )) # Int  |-> lst2_size_pre)
  **  ((( &( "lst1" ) )) # Ptr  |-> lst1_pre)
  **  ((( &( "lst2" ) )) # Ptr  |-> lst2_pre)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  (CharPtrArray2.missing_i lst1_pre lst1_size_pre i row_ptr rows1 )
  **  (((lst1_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_74 ((Znth (i) (rows1) ((@nil Z))))) )
  **  (CharPtrArray2.full lst2_pre lst2_size_pre rows2 )
|--
  “ (valid_string (row_payload_z_74 ((Znth (i) (rows1) ((@nil Z))))) ) ” 
  &&  “ ((string_length ((row_payload_z_74 ((Znth (i) (rows1) ((@nil Z))))))) < INT_MAX) ”
.

Definition total_match_partial_solve_wit_1_aux := 
forall (lst2_size_pre: Z) (lst2_pre: Z) (lst1_size_pre: Z) (lst1_pre: Z) (rows2: (@list (@list Z))) (rows1: (@list (@list Z))) (row_ptr: Z) (i: Z) (num2: Z) (len: Z) (num1: Z) (PreH1 : (0 <= i)) (PreH2 : (i < lst1_size_pre)) (PreH3 : (num2 = 0)) (PreH4 : (0 <= len)) (PreH5 : (len < INT_MAX)) (PreH6 : (rows_well_formed_74 rows1 lst1_size_pre )) (PreH7 : (rows_well_formed_74 rows2 lst2_size_pre )) (PreH8 : (problem_74_pre_z rows1 rows2 )) (PreH9 : (total_prefix_state_74 rows1 i num1 )) (PreH10 : (valid_string (row_payload_z_74 ((Znth (i) (rows1) ((@nil Z))))) )) (PreH11 : ((string_length ((row_payload_z_74 ((Znth (i) (rows1) ((@nil Z))))))) < INT_MAX)) (PreH12 : ((Zlength ((Znth (i) (rows1) ((@nil Z))))) = ((string_length ((row_payload_z_74 ((Znth (i) (rows1) ((@nil Z))))))) + 1 ))) (PreH13 : (0 <= (rows_total_len_z_74 (rows1)))) (PreH14 : ((rows_total_len_z_74 (rows1)) <= INT_MAX)) (PreH15 : (0 <= (rows_total_len_z_74 (rows2)))) (PreH16 : ((rows_total_len_z_74 (rows2)) <= INT_MAX)) ,
  (CharPtrArray2.missing_i lst1_pre lst1_size_pre i row_ptr rows1 )
  **  (((lst1_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_74 ((Znth (i) (rows1) ((@nil Z))))) )
  **  (CharPtrArray2.full lst2_pre lst2_size_pre rows2 )
|--
  “ (valid_string (row_payload_z_74 ((Znth (i) (rows1) ((@nil Z))))) ) ” 
  &&  “ ((string_length ((row_payload_z_74 ((Znth (i) (rows1) ((@nil Z))))))) < INT_MAX) ” 
  &&  “ (0 <= ((string_length ((row_payload_z_74 ((Znth (i) (rows1) ((@nil Z))))))) + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < lst1_size_pre) ” 
  &&  “ (num2 = 0) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (rows_well_formed_74 rows1 lst1_size_pre ) ” 
  &&  “ (rows_well_formed_74 rows2 lst2_size_pre ) ” 
  &&  “ (problem_74_pre_z rows1 rows2 ) ” 
  &&  “ (total_prefix_state_74 rows1 i num1 ) ” 
  &&  “ (valid_string (row_payload_z_74 ((Znth (i) (rows1) ((@nil Z))))) ) ” 
  &&  “ ((string_length ((row_payload_z_74 ((Znth (i) (rows1) ((@nil Z))))))) < INT_MAX) ” 
  &&  “ ((Zlength ((Znth (i) (rows1) ((@nil Z))))) = ((string_length ((row_payload_z_74 ((Znth (i) (rows1) ((@nil Z))))))) + 1 )) ” 
  &&  “ (0 <= (rows_total_len_z_74 (rows1))) ” 
  &&  “ ((rows_total_len_z_74 (rows1)) <= INT_MAX) ” 
  &&  “ (0 <= (rows_total_len_z_74 (rows2))) ” 
  &&  “ ((rows_total_len_z_74 (rows2)) <= INT_MAX) ”
  &&  (store_string row_ptr (row_payload_z_74 ((Znth (i) (rows1) ((@nil Z))))) )
  **  (CharPtrArray2.missing_i lst1_pre lst1_size_pre i row_ptr rows1 )
  **  (((lst1_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharPtrArray2.full lst2_pre lst2_size_pre rows2 )
.

Definition total_match_partial_solve_wit_1 := total_match_partial_solve_wit_1_pure -> total_match_partial_solve_wit_1_aux.

Definition total_match_partial_solve_wit_2_pure := 
forall (lst2_size_pre: Z) (lst2_pre: Z) (lst1_size_pre: Z) (lst1_pre: Z) (rows2: (@list (@list Z))) (rows1: (@list (@list Z))) (row_ptr: Z) (i: Z) (num1: Z) (len: Z) (num2: Z) (PreH1 : (0 <= i)) (PreH2 : (i < lst2_size_pre)) (PreH3 : (num1 = (rows_total_len_z_74 (rows1)))) (PreH4 : (0 <= len)) (PreH5 : (len < INT_MAX)) (PreH6 : (rows_well_formed_74 rows1 lst1_size_pre )) (PreH7 : (rows_well_formed_74 rows2 lst2_size_pre )) (PreH8 : (problem_74_pre_z rows1 rows2 )) (PreH9 : (total_prefix_state_74 rows2 i num2 )) (PreH10 : (valid_string (row_payload_z_74 ((Znth (i) (rows2) ((@nil Z))))) )) (PreH11 : ((string_length ((row_payload_z_74 ((Znth (i) (rows2) ((@nil Z))))))) < INT_MAX)) (PreH12 : ((Zlength ((Znth (i) (rows2) ((@nil Z))))) = ((string_length ((row_payload_z_74 ((Znth (i) (rows2) ((@nil Z))))))) + 1 ))) (PreH13 : (0 <= (rows_total_len_z_74 (rows1)))) (PreH14 : ((rows_total_len_z_74 (rows1)) <= INT_MAX)) (PreH15 : (0 <= (rows_total_len_z_74 (rows2)))) (PreH16 : ((rows_total_len_z_74 (rows2)) <= INT_MAX)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lst1_size" ) )) # Int  |-> lst1_size_pre)
  **  ((( &( "lst2_size" ) )) # Int  |-> lst2_size_pre)
  **  ((( &( "lst1" ) )) # Ptr  |-> lst1_pre)
  **  ((( &( "lst2" ) )) # Ptr  |-> lst2_pre)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  (CharPtrArray2.full lst1_pre lst1_size_pre rows1 )
  **  (CharPtrArray2.missing_i lst2_pre lst2_size_pre i row_ptr rows2 )
  **  (((lst2_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_74 ((Znth (i) (rows2) ((@nil Z))))) )
|--
  “ (valid_string (row_payload_z_74 ((Znth (i) (rows2) ((@nil Z))))) ) ” 
  &&  “ ((string_length ((row_payload_z_74 ((Znth (i) (rows2) ((@nil Z))))))) < INT_MAX) ”
.

Definition total_match_partial_solve_wit_2_aux := 
forall (lst2_size_pre: Z) (lst2_pre: Z) (lst1_size_pre: Z) (lst1_pre: Z) (rows2: (@list (@list Z))) (rows1: (@list (@list Z))) (row_ptr: Z) (i: Z) (num1: Z) (len: Z) (num2: Z) (PreH1 : (0 <= i)) (PreH2 : (i < lst2_size_pre)) (PreH3 : (num1 = (rows_total_len_z_74 (rows1)))) (PreH4 : (0 <= len)) (PreH5 : (len < INT_MAX)) (PreH6 : (rows_well_formed_74 rows1 lst1_size_pre )) (PreH7 : (rows_well_formed_74 rows2 lst2_size_pre )) (PreH8 : (problem_74_pre_z rows1 rows2 )) (PreH9 : (total_prefix_state_74 rows2 i num2 )) (PreH10 : (valid_string (row_payload_z_74 ((Znth (i) (rows2) ((@nil Z))))) )) (PreH11 : ((string_length ((row_payload_z_74 ((Znth (i) (rows2) ((@nil Z))))))) < INT_MAX)) (PreH12 : ((Zlength ((Znth (i) (rows2) ((@nil Z))))) = ((string_length ((row_payload_z_74 ((Znth (i) (rows2) ((@nil Z))))))) + 1 ))) (PreH13 : (0 <= (rows_total_len_z_74 (rows1)))) (PreH14 : ((rows_total_len_z_74 (rows1)) <= INT_MAX)) (PreH15 : (0 <= (rows_total_len_z_74 (rows2)))) (PreH16 : ((rows_total_len_z_74 (rows2)) <= INT_MAX)) ,
  (CharPtrArray2.full lst1_pre lst1_size_pre rows1 )
  **  (CharPtrArray2.missing_i lst2_pre lst2_size_pre i row_ptr rows2 )
  **  (((lst2_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_74 ((Znth (i) (rows2) ((@nil Z))))) )
|--
  “ (valid_string (row_payload_z_74 ((Znth (i) (rows2) ((@nil Z))))) ) ” 
  &&  “ ((string_length ((row_payload_z_74 ((Znth (i) (rows2) ((@nil Z))))))) < INT_MAX) ” 
  &&  “ (0 <= ((string_length ((row_payload_z_74 ((Znth (i) (rows2) ((@nil Z))))))) + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < lst2_size_pre) ” 
  &&  “ (num1 = (rows_total_len_z_74 (rows1))) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (rows_well_formed_74 rows1 lst1_size_pre ) ” 
  &&  “ (rows_well_formed_74 rows2 lst2_size_pre ) ” 
  &&  “ (problem_74_pre_z rows1 rows2 ) ” 
  &&  “ (total_prefix_state_74 rows2 i num2 ) ” 
  &&  “ (valid_string (row_payload_z_74 ((Znth (i) (rows2) ((@nil Z))))) ) ” 
  &&  “ ((string_length ((row_payload_z_74 ((Znth (i) (rows2) ((@nil Z))))))) < INT_MAX) ” 
  &&  “ ((Zlength ((Znth (i) (rows2) ((@nil Z))))) = ((string_length ((row_payload_z_74 ((Znth (i) (rows2) ((@nil Z))))))) + 1 )) ” 
  &&  “ (0 <= (rows_total_len_z_74 (rows1))) ” 
  &&  “ ((rows_total_len_z_74 (rows1)) <= INT_MAX) ” 
  &&  “ (0 <= (rows_total_len_z_74 (rows2))) ” 
  &&  “ ((rows_total_len_z_74 (rows2)) <= INT_MAX) ”
  &&  (store_string row_ptr (row_payload_z_74 ((Znth (i) (rows2) ((@nil Z))))) )
  **  (CharPtrArray2.full lst1_pre lst1_size_pre rows1 )
  **  (CharPtrArray2.missing_i lst2_pre lst2_size_pre i row_ptr rows2 )
  **  (((lst2_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
.

Definition total_match_partial_solve_wit_2 := total_match_partial_solve_wit_2_pure -> total_match_partial_solve_wit_2_aux.

Definition total_match_partial_solve_wit_3 := 
forall (lst2_size_pre: Z) (lst2_pre: Z) (lst1_size_pre: Z) (lst1_pre: Z) (rows2: (@list (@list Z))) (rows1: (@list (@list Z))) (num2: Z) (len: Z) (num1: Z) (i: Z) (PreH1 : (i >= lst2_size_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= lst2_size_pre)) (PreH4 : (num1 = (rows_total_len_z_74 (rows1)))) (PreH5 : (0 <= len)) (PreH6 : (len < INT_MAX)) (PreH7 : (rows_well_formed_74 rows1 lst1_size_pre )) (PreH8 : (rows_well_formed_74 rows2 lst2_size_pre )) (PreH9 : (problem_74_pre_z rows1 rows2 )) (PreH10 : (total_prefix_state_74 rows2 i num2 )) (PreH11 : (0 <= (rows_total_len_z_74 (rows1)))) (PreH12 : ((rows_total_len_z_74 (rows1)) <= INT_MAX)) (PreH13 : (0 <= (rows_total_len_z_74 (rows2)))) (PreH14 : ((rows_total_len_z_74 (rows2)) <= INT_MAX)) ,
  (CharPtrArray2.full lst1_pre lst1_size_pre rows1 )
  **  (CharPtrArray2.full lst2_pre lst2_size_pre rows2 )
|--
  “ (i >= lst2_size_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= lst2_size_pre) ” 
  &&  “ (num1 = (rows_total_len_z_74 (rows1))) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (rows_well_formed_74 rows1 lst1_size_pre ) ” 
  &&  “ (rows_well_formed_74 rows2 lst2_size_pre ) ” 
  &&  “ (problem_74_pre_z rows1 rows2 ) ” 
  &&  “ (total_prefix_state_74 rows2 i num2 ) ” 
  &&  “ (0 <= (rows_total_len_z_74 (rows1))) ” 
  &&  “ ((rows_total_len_z_74 (rows1)) <= INT_MAX) ” 
  &&  “ (0 <= (rows_total_len_z_74 (rows2))) ” 
  &&  “ ((rows_total_len_z_74 (rows2)) <= INT_MAX) ”
  &&  (CharPtrArray2.full lst1_pre lst1_size_pre rows1 )
  **  (CharPtrArray2.full lst2_pre lst2_size_pre rows2 )
.

Module Type VC_Correct.

Include ptr_array2_Strategy_Correct.
Include char_array_Strategy_Correct.
Include string_Strategy_Correct.

Axiom proof_of_total_match_safety_wit_1 : total_match_safety_wit_1.
Axiom proof_of_total_match_safety_wit_2 : total_match_safety_wit_2.
Axiom proof_of_total_match_safety_wit_3 : total_match_safety_wit_3.
Axiom proof_of_total_match_safety_wit_4 : total_match_safety_wit_4.
Axiom proof_of_total_match_safety_wit_5 : total_match_safety_wit_5.
Axiom proof_of_total_match_safety_wit_6 : total_match_safety_wit_6.
Axiom proof_of_total_match_safety_wit_7 : total_match_safety_wit_7.
Axiom proof_of_total_match_safety_wit_8 : total_match_safety_wit_8.
Axiom proof_of_total_match_safety_wit_9 : total_match_safety_wit_9.
Axiom proof_of_total_match_safety_wit_10 : total_match_safety_wit_10.
Axiom proof_of_total_match_entail_wit_1 : total_match_entail_wit_1.
Axiom proof_of_total_match_entail_wit_2 : total_match_entail_wit_2.
Axiom proof_of_total_match_entail_wit_3 : total_match_entail_wit_3.
Axiom proof_of_total_match_entail_wit_4 : total_match_entail_wit_4.
Axiom proof_of_total_match_entail_wit_5 : total_match_entail_wit_5.
Axiom proof_of_total_match_entail_wit_6 : total_match_entail_wit_6.
Axiom proof_of_total_match_entail_wit_7 : total_match_entail_wit_7.
Axiom proof_of_total_match_entail_wit_8 : total_match_entail_wit_8.
Axiom proof_of_total_match_return_wit_1 : total_match_return_wit_1.
Axiom proof_of_total_match_return_wit_2 : total_match_return_wit_2.
Axiom proof_of_total_match_partial_solve_wit_1_pure : total_match_partial_solve_wit_1_pure.
Axiom proof_of_total_match_partial_solve_wit_1 : total_match_partial_solve_wit_1.
Axiom proof_of_total_match_partial_solve_wit_2_pure : total_match_partial_solve_wit_2_pure.
Axiom proof_of_total_match_partial_solve_wit_2 : total_match_partial_solve_wit_2.
Axiom proof_of_total_match_partial_solve_wit_3 : total_match_partial_solve_wit_3.

End VC_Correct.
