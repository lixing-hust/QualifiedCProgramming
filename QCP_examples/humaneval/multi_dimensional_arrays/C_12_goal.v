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
Require Import coins_12.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import ptr_array2_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import ptr_array2_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_proof.
Require Import string_strategy_goal.
Require Import string_strategy_proof.

(*----- Function longest -----*)

Definition longest_safety_wit_1 := 
forall (strings_size_pre: Z) (strings_pre: Z) (rows: (@list (@list Z))) (PreH1 : (0 <= strings_size_pre)) (PreH2 : (strings_size_pre <= 100)) (PreH3 : (rows_well_formed_12 rows strings_size_pre )) (PreH4 : (problem_12_pre_z rows )) ,
  ((( &( "strings_size" ) )) # Int  |-> strings_size_pre)
  **  ((( &( "strings" ) )) # Ptr  |-> strings_pre)
  **  (CharPtrArray2.full strings_pre strings_size_pre rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition longest_safety_wit_2 := 
forall (strings_size_pre: Z) (strings_pre: Z) (rows: (@list (@list Z))) (PreH1 : (strings_size_pre = 0)) (PreH2 : (0 <= strings_size_pre)) (PreH3 : (strings_size_pre <= 100)) (PreH4 : (rows_well_formed_12 rows strings_size_pre )) (PreH5 : (problem_12_pre_z rows )) ,
  ((( &( "strings_size" ) )) # Int  |-> strings_size_pre)
  **  ((( &( "strings" ) )) # Ptr  |-> strings_pre)
  **  (CharPtrArray2.full strings_pre strings_size_pre rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition longest_safety_wit_3 := 
forall (strings_size_pre: Z) (strings_pre: Z) (rows: (@list (@list Z))) (PreH1 : (strings_size_pre <> 0)) (PreH2 : (0 <= strings_size_pre)) (PreH3 : (strings_size_pre <= 100)) (PreH4 : (rows_well_formed_12 rows strings_size_pre )) (PreH5 : (problem_12_pre_z rows )) ,
  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "strings_size" ) )) # Int  |-> strings_size_pre)
  **  ((( &( "strings" ) )) # Ptr  |-> strings_pre)
  **  (CharPtrArray2.full strings_pre strings_size_pre rows )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition longest_safety_wit_4 := 
forall (strings_size_pre: Z) (strings_pre: Z) (rows: (@list (@list Z))) (PreH1 : (strings_size_pre <> 0)) (PreH2 : (0 <= strings_size_pre)) (PreH3 : (strings_size_pre <= 100)) (PreH4 : (rows_well_formed_12 rows strings_size_pre )) (PreH5 : (problem_12_pre_z rows )) ,
  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "strings_size" ) )) # Int  |-> strings_size_pre)
  **  ((( &( "strings" ) )) # Ptr  |-> strings_pre)
  **  (CharPtrArray2.full strings_pre strings_size_pre rows )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition longest_safety_wit_5 := 
forall (strings_size_pre: Z) (strings_pre: Z) (rows: (@list (@list Z))) (PreH1 : (strings_size_pre <> 0)) (PreH2 : (0 <= strings_size_pre)) (PreH3 : (strings_size_pre <= 100)) (PreH4 : (rows_well_formed_12 rows strings_size_pre )) (PreH5 : (problem_12_pre_z rows )) ,
  ((( &( "best_idx" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |-> (-1))
  **  ((( &( "strings_size" ) )) # Int  |-> strings_size_pre)
  **  ((( &( "strings" ) )) # Ptr  |-> strings_pre)
  **  (CharPtrArray2.full strings_pre strings_size_pre rows )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition longest_safety_wit_6 := 
forall (strings_size_pre: Z) (strings_pre: Z) (rows: (@list (@list Z))) (PreH1 : (strings_size_pre <> 0)) (PreH2 : (0 <= strings_size_pre)) (PreH3 : (strings_size_pre <= 100)) (PreH4 : (rows_well_formed_12 rows strings_size_pre )) (PreH5 : (problem_12_pre_z rows )) ,
  ((( &( "best_idx" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |-> (-1))
  **  ((( &( "strings_size" ) )) # Int  |-> strings_size_pre)
  **  ((( &( "strings" ) )) # Ptr  |-> strings_pre)
  **  (CharPtrArray2.full strings_pre strings_size_pre rows )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition longest_safety_wit_7 := 
forall (strings_size_pre: Z) (strings_pre: Z) (rows: (@list (@list Z))) (PreH1 : (strings_size_pre <> 0)) (PreH2 : (0 <= strings_size_pre)) (PreH3 : (strings_size_pre <= 100)) (PreH4 : (rows_well_formed_12 rows strings_size_pre )) (PreH5 : (problem_12_pre_z rows )) ,
  ((( &( "len" ) )) # Int  |->_)
  **  ((( &( "best_idx" ) )) # Int  |-> (-1))
  **  ((( &( "best" ) )) # Int  |-> (-1))
  **  ((( &( "strings_size" ) )) # Int  |-> strings_size_pre)
  **  ((( &( "strings" ) )) # Ptr  |-> strings_pre)
  **  (CharPtrArray2.full strings_pre strings_size_pre rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition longest_safety_wit_8 := 
forall (strings_size_pre: Z) (strings_pre: Z) (rows: (@list (@list Z))) (PreH1 : (strings_size_pre <> 0)) (PreH2 : (0 <= strings_size_pre)) (PreH3 : (strings_size_pre <= 100)) (PreH4 : (rows_well_formed_12 rows strings_size_pre )) (PreH5 : (problem_12_pre_z rows )) ,
  ((( &( "cur" ) )) # Ptr  |->_)
  **  ((( &( "len" ) )) # Int  |-> 0)
  **  ((( &( "best_idx" ) )) # Int  |-> (-1))
  **  ((( &( "best" ) )) # Int  |-> (-1))
  **  ((( &( "strings_size" ) )) # Int  |-> strings_size_pre)
  **  ((( &( "strings" ) )) # Ptr  |-> strings_pre)
  **  (CharPtrArray2.full strings_pre strings_size_pre rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition longest_safety_wit_9 := 
forall (strings_size_pre: Z) (strings_pre: Z) (rows: (@list (@list Z))) (PreH1 : (strings_size_pre <> 0)) (PreH2 : (0 <= strings_size_pre)) (PreH3 : (strings_size_pre <= 100)) (PreH4 : (rows_well_formed_12 rows strings_size_pre )) (PreH5 : (problem_12_pre_z rows )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Ptr  |-> 0)
  **  ((( &( "len" ) )) # Int  |-> 0)
  **  ((( &( "best_idx" ) )) # Int  |-> (-1))
  **  ((( &( "best" ) )) # Int  |-> (-1))
  **  ((( &( "strings_size" ) )) # Int  |-> strings_size_pre)
  **  ((( &( "strings" ) )) # Ptr  |-> strings_pre)
  **  (CharPtrArray2.full strings_pre strings_size_pre rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition longest_safety_wit_10 := 
forall (strings_size_pre: Z) (strings_pre: Z) (rows: (@list (@list Z))) (i: Z) (cur: Z) (len: Z) (best: Z) (best_idx: Z) (PreH1 : (0 <= i)) (PreH2 : (i < strings_size_pre)) (PreH3 : (0 < strings_size_pre)) (PreH4 : (strings_size_pre <= 100)) (PreH5 : (0 <= len)) (PreH6 : (len < INT_MAX)) (PreH7 : (rows_well_formed_12 rows strings_size_pre )) (PreH8 : (problem_12_pre_z rows )) (PreH9 : (longest_prefix_z_12 rows (i + 1 ) best_idx best )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "strings_size" ) )) # Int  |-> strings_size_pre)
  **  ((( &( "strings" ) )) # Ptr  |-> strings_pre)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "best_idx" ) )) # Int  |-> best_idx)
  **  (CharPtrArray2.full strings_pre strings_size_pre rows )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition longest_entail_wit_1 := 
(
forall (strings_size_pre: Z) (strings_pre: Z) (rows: (@list (@list Z))) (PreH1 : (strings_size_pre <> 0)) (PreH2 : (0 <= strings_size_pre)) (PreH3 : (strings_size_pre <= 100)) (PreH4 : (rows_well_formed_12 rows strings_size_pre )) (PreH5 : (problem_12_pre_z rows )) ,
  (CharPtrArray2.full strings_pre strings_size_pre rows )
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= strings_size_pre) ” 
  &&  “ (0 < strings_size_pre) ” 
  &&  “ (strings_size_pre <= 100) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 < INT_MAX) ” 
  &&  “ (rows_well_formed_12 rows strings_size_pre ) ” 
  &&  “ (problem_12_pre_z rows ) ” 
  &&  “ (longest_prefix_z_12 rows 0 (-1) (-1) ) ”
  &&  (CharPtrArray2.full strings_pre strings_size_pre rows )
) \/
(
forall (strings_size_pre: Z) (rows: (@list (@list Z))) (PreH1 : (strings_size_pre <> 0)) (PreH2 : (0 <= strings_size_pre)) (PreH3 : (strings_size_pre <= 100)) (PreH4 : (rows_well_formed_12 rows strings_size_pre )) (PreH5 : (problem_12_pre_z rows )) ,
  TT && emp 
|--
  “ (longest_prefix_z_12 rows 0 (-1) (-1) ) ”
  &&  emp
).

Definition longest_entail_wit_1_split_goal_1 := 
forall (strings_size_pre: Z) (rows: (@list (@list Z))) (PreH1 : (strings_size_pre <> 0)) (PreH2 : (0 <= strings_size_pre)) (PreH3 : (strings_size_pre <= 100)) (PreH4 : (rows_well_formed_12 rows strings_size_pre )) (PreH5 : (problem_12_pre_z rows )) ,
  TT && emp 
|--
  “ (longest_prefix_z_12 rows 0 (-1) (-1) ) ”
.

Definition longest_entail_wit_2 := 
(
forall (strings_size_pre: Z) (strings_pre: Z) (rows: (@list (@list Z))) (best_idx: Z) (best: Z) (len: Z) (i: Z) (PreH1 : (i < strings_size_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= strings_size_pre)) (PreH4 : (0 < strings_size_pre)) (PreH5 : (strings_size_pre <= 100)) (PreH6 : (0 <= len)) (PreH7 : (len < INT_MAX)) (PreH8 : (rows_well_formed_12 rows strings_size_pre )) (PreH9 : (problem_12_pre_z rows )) (PreH10 : (longest_prefix_z_12 rows i best_idx best )) ,
  (CharPtrArray2.full strings_pre strings_size_pre rows )
|--
  EX (row_ptr: Z) ,
  “ (0 <= i) ” 
  &&  “ (i < strings_size_pre) ” 
  &&  “ (0 < strings_size_pre) ” 
  &&  “ (strings_size_pre <= 100) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (rows_well_formed_12 rows strings_size_pre ) ” 
  &&  “ (problem_12_pre_z rows ) ” 
  &&  “ (longest_prefix_z_12 rows i best_idx best ) ”
  &&  (CharPtrArray2.missing_i strings_pre strings_size_pre i row_ptr rows )
  **  (((strings_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
) \/
(
forall (strings_size_pre: Z) (rows: (@list (@list Z))) (best_idx: Z) (best: Z) (len: Z) (i: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (0 <= (Zlength ((Znth i rows __default__List_Z))))) (PreH2 : (i < strings_size_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= strings_size_pre)) (PreH5 : (0 < strings_size_pre)) (PreH6 : (strings_size_pre <= 100)) (PreH7 : (0 <= len)) (PreH8 : (len < INT_MAX)) (PreH9 : (rows_well_formed_12 rows strings_size_pre )) (PreH10 : (problem_12_pre_z rows )) (PreH11 : (longest_prefix_z_12 rows i best_idx best )) ,
  (CharArray.full row_ptr_2 (Zlength ((Znth i rows __default__List_Z))) (Znth i rows __default__List_Z) )
|--
  (CharArray.full row_ptr_2 (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
).

Definition longest_entail_wit_2_split_goal_spatial := 
forall (strings_size_pre: Z) (rows: (@list (@list Z))) (best_idx: Z) (best: Z) (len: Z) (i: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (0 <= (Zlength ((Znth i rows __default__List_Z))))) (PreH2 : (i < strings_size_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= strings_size_pre)) (PreH5 : (0 < strings_size_pre)) (PreH6 : (strings_size_pre <= 100)) (PreH7 : (0 <= len)) (PreH8 : (len < INT_MAX)) (PreH9 : (rows_well_formed_12 rows strings_size_pre )) (PreH10 : (problem_12_pre_z rows )) (PreH11 : (longest_prefix_z_12 rows i best_idx best )) ,
  (CharArray.full row_ptr_2 (Zlength ((Znth i rows __default__List_Z))) (Znth i rows __default__List_Z) )
|--
  (CharArray.full row_ptr_2 (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
.

Definition longest_entail_wit_3 := 
(
forall (strings_size_pre: Z) (strings_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (i: Z) (len: Z) (best: Z) (best_idx: Z) (PreH1 : (0 <= i)) (PreH2 : (i < strings_size_pre)) (PreH3 : (0 < strings_size_pre)) (PreH4 : (strings_size_pre <= 100)) (PreH5 : (0 <= len)) (PreH6 : (len < INT_MAX)) (PreH7 : (rows_well_formed_12 rows strings_size_pre )) (PreH8 : (problem_12_pre_z rows )) (PreH9 : (longest_prefix_z_12 rows i best_idx best )) ,
  (CharPtrArray2.missing_i strings_pre strings_size_pre i row_ptr rows )
  **  (((strings_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
|--
  “ (0 <= i) ” 
  &&  “ (i < strings_size_pre) ” 
  &&  “ (0 < strings_size_pre) ” 
  &&  “ (strings_size_pre <= 100) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (rows_well_formed_12 rows strings_size_pre ) ” 
  &&  “ (problem_12_pre_z rows ) ” 
  &&  “ (longest_prefix_z_12 rows i best_idx best ) ” 
  &&  “ (valid_string (row_payload_z_12 ((Znth (i) (rows) ((@nil Z))))) ) ” 
  &&  “ ((string_length ((row_payload_z_12 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX) ” 
  &&  “ ((Zlength ((Znth (i) (rows) ((@nil Z))))) = ((string_length ((row_payload_z_12 ((Znth (i) (rows) ((@nil Z))))))) + 1 )) ”
  &&  (CharPtrArray2.missing_i strings_pre strings_size_pre i row_ptr rows )
  **  (((strings_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_12 ((Znth (i) (rows) ((@nil Z))))) )
) \/
(
forall (strings_size_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (i: Z) (len: Z) (best: Z) (best_idx: Z) (PreH1 : (0 <= (Zlength ((Znth (i) (rows) ((@nil Z))))))) (PreH2 : (0 <= i)) (PreH3 : (i < strings_size_pre)) (PreH4 : (0 < strings_size_pre)) (PreH5 : (strings_size_pre <= 100)) (PreH6 : (0 <= len)) (PreH7 : (len < INT_MAX)) (PreH8 : (rows_well_formed_12 rows strings_size_pre )) (PreH9 : (problem_12_pre_z rows )) (PreH10 : (longest_prefix_z_12 rows i best_idx best )) ,
  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
|--
  “ ((Zlength ((Znth (i) (rows) ((@nil Z))))) = ((string_length ((row_payload_z_12 ((Znth (i) (rows) ((@nil Z))))))) + 1 )) ” 
  &&  “ ((string_length ((row_payload_z_12 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX) ” 
  &&  “ (valid_string (row_payload_z_12 ((Znth (i) (rows) ((@nil Z))))) ) ”
  &&  (CharArray.full row_ptr ((string_length ((row_payload_z_12 ((Znth (i) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_12 ((Znth (i) (rows) ((@nil Z))))))) )
).

Definition longest_entail_wit_3_split_goal_1 := 
forall (strings_size_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (i: Z) (len: Z) (best: Z) (best_idx: Z) (PreH1 : (0 <= (Zlength ((Znth (i) (rows) ((@nil Z))))))) (PreH2 : (0 <= i)) (PreH3 : (i < strings_size_pre)) (PreH4 : (0 < strings_size_pre)) (PreH5 : (strings_size_pre <= 100)) (PreH6 : (0 <= len)) (PreH7 : (len < INT_MAX)) (PreH8 : (rows_well_formed_12 rows strings_size_pre )) (PreH9 : (problem_12_pre_z rows )) (PreH10 : (longest_prefix_z_12 rows i best_idx best )) ,
  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
|--
  “ ((Zlength ((Znth (i) (rows) ((@nil Z))))) = ((string_length ((row_payload_z_12 ((Znth (i) (rows) ((@nil Z))))))) + 1 )) ”
.

Definition longest_entail_wit_3_split_goal_2 := 
forall (strings_size_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (i: Z) (len: Z) (best: Z) (best_idx: Z) (PreH1 : (0 <= (Zlength ((Znth (i) (rows) ((@nil Z))))))) (PreH2 : (0 <= i)) (PreH3 : (i < strings_size_pre)) (PreH4 : (0 < strings_size_pre)) (PreH5 : (strings_size_pre <= 100)) (PreH6 : (0 <= len)) (PreH7 : (len < INT_MAX)) (PreH8 : (rows_well_formed_12 rows strings_size_pre )) (PreH9 : (problem_12_pre_z rows )) (PreH10 : (longest_prefix_z_12 rows i best_idx best )) ,
  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
|--
  “ ((string_length ((row_payload_z_12 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX) ”
.

Definition longest_entail_wit_3_split_goal_3 := 
forall (strings_size_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (i: Z) (len: Z) (best: Z) (best_idx: Z) (PreH1 : (0 <= (Zlength ((Znth (i) (rows) ((@nil Z))))))) (PreH2 : (0 <= i)) (PreH3 : (i < strings_size_pre)) (PreH4 : (0 < strings_size_pre)) (PreH5 : (strings_size_pre <= 100)) (PreH6 : (0 <= len)) (PreH7 : (len < INT_MAX)) (PreH8 : (rows_well_formed_12 rows strings_size_pre )) (PreH9 : (problem_12_pre_z rows )) (PreH10 : (longest_prefix_z_12 rows i best_idx best )) ,
  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
|--
  “ (valid_string (row_payload_z_12 ((Znth (i) (rows) ((@nil Z))))) ) ”
.

Definition longest_entail_wit_3_split_goal_spatial := 
forall (strings_size_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (i: Z) (len: Z) (best: Z) (best_idx: Z) (PreH1 : (0 <= (Zlength ((Znth (i) (rows) ((@nil Z))))))) (PreH2 : (0 <= i)) (PreH3 : (i < strings_size_pre)) (PreH4 : (0 < strings_size_pre)) (PreH5 : (strings_size_pre <= 100)) (PreH6 : (0 <= len)) (PreH7 : (len < INT_MAX)) (PreH8 : (rows_well_formed_12 rows strings_size_pre )) (PreH9 : (problem_12_pre_z rows )) (PreH10 : (longest_prefix_z_12 rows i best_idx best )) ,
  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
|--
  (CharArray.full row_ptr ((string_length ((row_payload_z_12 ((Znth (i) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_12 ((Znth (i) (rows) ((@nil Z))))))) )
.

Definition longest_entail_wit_4 := 
(
forall (strings_size_pre: Z) (strings_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (i: Z) (len: Z) (best: Z) (best_idx: Z) (retval: Z) (PreH1 : (retval = (string_length ((row_payload_z_12 ((Znth (i) (rows) ((@nil Z))))))))) (PreH2 : (0 <= ((string_length ((row_payload_z_12 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < strings_size_pre)) (PreH5 : (0 < strings_size_pre)) (PreH6 : (strings_size_pre <= 100)) (PreH7 : (0 <= len)) (PreH8 : (len < INT_MAX)) (PreH9 : (rows_well_formed_12 rows strings_size_pre )) (PreH10 : (problem_12_pre_z rows )) (PreH11 : (longest_prefix_z_12 rows i best_idx best )) (PreH12 : (valid_string (row_payload_z_12 ((Znth (i) (rows) ((@nil Z))))) )) (PreH13 : ((string_length ((row_payload_z_12 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX)) (PreH14 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = ((string_length ((row_payload_z_12 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) ,
  (store_string row_ptr (row_payload_z_12 ((Znth (i) (rows) ((@nil Z))))) )
  **  (CharPtrArray2.missing_i strings_pre strings_size_pre i row_ptr rows )
  **  (((strings_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ (0 <= i) ” 
  &&  “ (i < strings_size_pre) ” 
  &&  “ (0 < strings_size_pre) ” 
  &&  “ (strings_size_pre <= 100) ” 
  &&  “ (retval = (row_len_z_12 ((Znth (i) (rows) ((@nil Z)))))) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < INT_MAX) ” 
  &&  “ (rows_well_formed_12 rows strings_size_pre ) ” 
  &&  “ (problem_12_pre_z rows ) ” 
  &&  “ (longest_prefix_z_12 rows i best_idx best ) ”
  &&  (CharPtrArray2.missing_i strings_pre strings_size_pre i row_ptr rows )
  **  (((strings_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
) \/
(
forall (strings_size_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (i: Z) (len: Z) (best: Z) (best_idx: Z) (retval: Z) (PreH1 : (retval = (string_length ((row_payload_z_12 ((Znth (i) (rows) ((@nil Z))))))))) (PreH2 : (0 <= ((string_length ((row_payload_z_12 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < strings_size_pre)) (PreH5 : (0 < strings_size_pre)) (PreH6 : (strings_size_pre <= 100)) (PreH7 : (0 <= len)) (PreH8 : (len < INT_MAX)) (PreH9 : (rows_well_formed_12 rows strings_size_pre )) (PreH10 : (problem_12_pre_z rows )) (PreH11 : (longest_prefix_z_12 rows i best_idx best )) (PreH12 : (valid_string (row_payload_z_12 ((Znth (i) (rows) ((@nil Z))))) )) (PreH13 : ((string_length ((row_payload_z_12 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX)) (PreH14 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = ((string_length ((row_payload_z_12 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) ,
  (CharArray.full row_ptr ((string_length ((row_payload_z_12 ((Znth (i) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_12 ((Znth (i) (rows) ((@nil Z))))))) )
|--
  “ (0 <= retval) ” 
  &&  “ (retval = (row_len_z_12 ((Znth (i) (rows) ((@nil Z)))))) ”
  &&  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
).

Definition longest_entail_wit_4_split_goal_1 := 
forall (strings_size_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (i: Z) (len: Z) (best: Z) (best_idx: Z) (retval: Z) (PreH1 : (retval = (string_length ((row_payload_z_12 ((Znth (i) (rows) ((@nil Z))))))))) (PreH2 : (0 <= ((string_length ((row_payload_z_12 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < strings_size_pre)) (PreH5 : (0 < strings_size_pre)) (PreH6 : (strings_size_pre <= 100)) (PreH7 : (0 <= len)) (PreH8 : (len < INT_MAX)) (PreH9 : (rows_well_formed_12 rows strings_size_pre )) (PreH10 : (problem_12_pre_z rows )) (PreH11 : (longest_prefix_z_12 rows i best_idx best )) (PreH12 : (valid_string (row_payload_z_12 ((Znth (i) (rows) ((@nil Z))))) )) (PreH13 : ((string_length ((row_payload_z_12 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX)) (PreH14 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = ((string_length ((row_payload_z_12 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) ,
  (CharArray.full row_ptr ((string_length ((row_payload_z_12 ((Znth (i) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_12 ((Znth (i) (rows) ((@nil Z))))))) )
|--
  “ (0 <= retval) ”
.

Definition longest_entail_wit_4_split_goal_2 := 
forall (strings_size_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (i: Z) (len: Z) (best: Z) (best_idx: Z) (retval: Z) (PreH1 : (retval = (string_length ((row_payload_z_12 ((Znth (i) (rows) ((@nil Z))))))))) (PreH2 : (0 <= ((string_length ((row_payload_z_12 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < strings_size_pre)) (PreH5 : (0 < strings_size_pre)) (PreH6 : (strings_size_pre <= 100)) (PreH7 : (0 <= len)) (PreH8 : (len < INT_MAX)) (PreH9 : (rows_well_formed_12 rows strings_size_pre )) (PreH10 : (problem_12_pre_z rows )) (PreH11 : (longest_prefix_z_12 rows i best_idx best )) (PreH12 : (valid_string (row_payload_z_12 ((Znth (i) (rows) ((@nil Z))))) )) (PreH13 : ((string_length ((row_payload_z_12 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX)) (PreH14 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = ((string_length ((row_payload_z_12 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) ,
  (CharArray.full row_ptr ((string_length ((row_payload_z_12 ((Znth (i) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_12 ((Znth (i) (rows) ((@nil Z))))))) )
|--
  “ (retval = (row_len_z_12 ((Znth (i) (rows) ((@nil Z)))))) ”
.

Definition longest_entail_wit_4_split_goal_spatial := 
forall (strings_size_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (i: Z) (len: Z) (best: Z) (best_idx: Z) (retval: Z) (PreH1 : (retval = (string_length ((row_payload_z_12 ((Znth (i) (rows) ((@nil Z))))))))) (PreH2 : (0 <= ((string_length ((row_payload_z_12 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < strings_size_pre)) (PreH5 : (0 < strings_size_pre)) (PreH6 : (strings_size_pre <= 100)) (PreH7 : (0 <= len)) (PreH8 : (len < INT_MAX)) (PreH9 : (rows_well_formed_12 rows strings_size_pre )) (PreH10 : (problem_12_pre_z rows )) (PreH11 : (longest_prefix_z_12 rows i best_idx best )) (PreH12 : (valid_string (row_payload_z_12 ((Znth (i) (rows) ((@nil Z))))) )) (PreH13 : ((string_length ((row_payload_z_12 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX)) (PreH14 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = ((string_length ((row_payload_z_12 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) ,
  (CharArray.full row_ptr ((string_length ((row_payload_z_12 ((Znth (i) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_12 ((Znth (i) (rows) ((@nil Z))))))) )
|--
  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
.

Definition longest_entail_wit_5_1 := 
(
forall (strings_size_pre: Z) (strings_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (i: Z) (len: Z) (best: Z) (best_idx: Z) (PreH1 : (len <= best)) (PreH2 : (0 <= i)) (PreH3 : (i < strings_size_pre)) (PreH4 : (0 < strings_size_pre)) (PreH5 : (strings_size_pre <= 100)) (PreH6 : (len = (row_len_z_12 ((Znth (i) (rows) ((@nil Z))))))) (PreH7 : (0 <= len)) (PreH8 : (len < INT_MAX)) (PreH9 : (rows_well_formed_12 rows strings_size_pre )) (PreH10 : (problem_12_pre_z rows )) (PreH11 : (longest_prefix_z_12 rows i best_idx best )) ,
  (CharPtrArray2.missing_i strings_pre strings_size_pre i row_ptr rows )
  **  (((strings_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
|--
  “ (0 <= i) ” 
  &&  “ (i < strings_size_pre) ” 
  &&  “ (0 < strings_size_pre) ” 
  &&  “ (strings_size_pre <= 100) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (rows_well_formed_12 rows strings_size_pre ) ” 
  &&  “ (problem_12_pre_z rows ) ” 
  &&  “ (longest_prefix_z_12 rows (i + 1 ) best_idx best ) ”
  &&  (CharPtrArray2.full strings_pre strings_size_pre rows )
) \/
(
forall (strings_size_pre: Z) (strings_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (i: Z) (len: Z) (best: Z) (best_idx: Z) (PreH1 : (0 <= (Zlength ((Znth (i) (rows) ((@nil Z))))))) (PreH2 : (len <= best)) (PreH3 : (0 <= i)) (PreH4 : (i < strings_size_pre)) (PreH5 : (0 < strings_size_pre)) (PreH6 : (strings_size_pre <= 100)) (PreH7 : (len = (row_len_z_12 ((Znth (i) (rows) ((@nil Z))))))) (PreH8 : (0 <= len)) (PreH9 : (len < INT_MAX)) (PreH10 : (rows_well_formed_12 rows strings_size_pre )) (PreH11 : (problem_12_pre_z rows )) (PreH12 : (longest_prefix_z_12 rows i best_idx best )) ,
  (CharPtrArray2.missing_i strings_pre strings_size_pre i row_ptr rows )
  **  (((strings_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
|--
  “ (longest_prefix_z_12 rows (i + 1 ) best_idx best ) ”
  &&  (CharPtrArray2.full strings_pre strings_size_pre rows )
).

Definition longest_entail_wit_5_1_split_goal_1 := 
forall (strings_size_pre: Z) (strings_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (i: Z) (len: Z) (best: Z) (best_idx: Z) (PreH1 : (0 <= (Zlength ((Znth (i) (rows) ((@nil Z))))))) (PreH2 : (len <= best)) (PreH3 : (0 <= i)) (PreH4 : (i < strings_size_pre)) (PreH5 : (0 < strings_size_pre)) (PreH6 : (strings_size_pre <= 100)) (PreH7 : (len = (row_len_z_12 ((Znth (i) (rows) ((@nil Z))))))) (PreH8 : (0 <= len)) (PreH9 : (len < INT_MAX)) (PreH10 : (rows_well_formed_12 rows strings_size_pre )) (PreH11 : (problem_12_pre_z rows )) (PreH12 : (longest_prefix_z_12 rows i best_idx best )) ,
  (CharPtrArray2.missing_i strings_pre strings_size_pre i row_ptr rows )
  **  (((strings_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
|--
  “ (longest_prefix_z_12 rows (i + 1 ) best_idx best ) ”
.

Definition longest_entail_wit_5_1_split_goal_spatial := 
forall (strings_size_pre: Z) (strings_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (i: Z) (len: Z) (best: Z) (best_idx: Z) (PreH1 : (0 <= (Zlength ((Znth (i) (rows) ((@nil Z))))))) (PreH2 : (len <= best)) (PreH3 : (0 <= i)) (PreH4 : (i < strings_size_pre)) (PreH5 : (0 < strings_size_pre)) (PreH6 : (strings_size_pre <= 100)) (PreH7 : (len = (row_len_z_12 ((Znth (i) (rows) ((@nil Z))))))) (PreH8 : (0 <= len)) (PreH9 : (len < INT_MAX)) (PreH10 : (rows_well_formed_12 rows strings_size_pre )) (PreH11 : (problem_12_pre_z rows )) (PreH12 : (longest_prefix_z_12 rows i best_idx best )) ,
  (CharPtrArray2.missing_i strings_pre strings_size_pre i row_ptr rows )
  **  (((strings_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
|--
  (CharPtrArray2.full strings_pre strings_size_pre rows )
.

Definition longest_entail_wit_5_2 := 
(
forall (strings_size_pre: Z) (strings_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (i: Z) (len: Z) (best: Z) (best_idx: Z) (PreH1 : (len > best)) (PreH2 : (0 <= i)) (PreH3 : (i < strings_size_pre)) (PreH4 : (0 < strings_size_pre)) (PreH5 : (strings_size_pre <= 100)) (PreH6 : (len = (row_len_z_12 ((Znth (i) (rows) ((@nil Z))))))) (PreH7 : (0 <= len)) (PreH8 : (len < INT_MAX)) (PreH9 : (rows_well_formed_12 rows strings_size_pre )) (PreH10 : (problem_12_pre_z rows )) (PreH11 : (longest_prefix_z_12 rows i best_idx best )) ,
  (CharPtrArray2.missing_i strings_pre strings_size_pre i row_ptr rows )
  **  (((strings_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
|--
  “ (0 <= i) ” 
  &&  “ (i < strings_size_pre) ” 
  &&  “ (0 < strings_size_pre) ” 
  &&  “ (strings_size_pre <= 100) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (rows_well_formed_12 rows strings_size_pre ) ” 
  &&  “ (problem_12_pre_z rows ) ” 
  &&  “ (longest_prefix_z_12 rows (i + 1 ) i len ) ”
  &&  (CharPtrArray2.full strings_pre strings_size_pre rows )
) \/
(
forall (strings_size_pre: Z) (strings_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (i: Z) (len: Z) (best: Z) (best_idx: Z) (PreH1 : (0 <= (Zlength ((Znth (i) (rows) ((@nil Z))))))) (PreH2 : (len > best)) (PreH3 : (0 <= i)) (PreH4 : (i < strings_size_pre)) (PreH5 : (0 < strings_size_pre)) (PreH6 : (strings_size_pre <= 100)) (PreH7 : (len = (row_len_z_12 ((Znth (i) (rows) ((@nil Z))))))) (PreH8 : (0 <= len)) (PreH9 : (len < INT_MAX)) (PreH10 : (rows_well_formed_12 rows strings_size_pre )) (PreH11 : (problem_12_pre_z rows )) (PreH12 : (longest_prefix_z_12 rows i best_idx best )) ,
  (CharPtrArray2.missing_i strings_pre strings_size_pre i row_ptr rows )
  **  (((strings_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
|--
  “ (longest_prefix_z_12 rows (i + 1 ) i len ) ”
  &&  (CharPtrArray2.full strings_pre strings_size_pre rows )
).

Definition longest_entail_wit_5_2_split_goal_1 := 
forall (strings_size_pre: Z) (strings_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (i: Z) (len: Z) (best: Z) (best_idx: Z) (PreH1 : (0 <= (Zlength ((Znth (i) (rows) ((@nil Z))))))) (PreH2 : (len > best)) (PreH3 : (0 <= i)) (PreH4 : (i < strings_size_pre)) (PreH5 : (0 < strings_size_pre)) (PreH6 : (strings_size_pre <= 100)) (PreH7 : (len = (row_len_z_12 ((Znth (i) (rows) ((@nil Z))))))) (PreH8 : (0 <= len)) (PreH9 : (len < INT_MAX)) (PreH10 : (rows_well_formed_12 rows strings_size_pre )) (PreH11 : (problem_12_pre_z rows )) (PreH12 : (longest_prefix_z_12 rows i best_idx best )) ,
  (CharPtrArray2.missing_i strings_pre strings_size_pre i row_ptr rows )
  **  (((strings_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
|--
  “ (longest_prefix_z_12 rows (i + 1 ) i len ) ”
.

Definition longest_entail_wit_5_2_split_goal_spatial := 
forall (strings_size_pre: Z) (strings_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (i: Z) (len: Z) (best: Z) (best_idx: Z) (PreH1 : (0 <= (Zlength ((Znth (i) (rows) ((@nil Z))))))) (PreH2 : (len > best)) (PreH3 : (0 <= i)) (PreH4 : (i < strings_size_pre)) (PreH5 : (0 < strings_size_pre)) (PreH6 : (strings_size_pre <= 100)) (PreH7 : (len = (row_len_z_12 ((Znth (i) (rows) ((@nil Z))))))) (PreH8 : (0 <= len)) (PreH9 : (len < INT_MAX)) (PreH10 : (rows_well_formed_12 rows strings_size_pre )) (PreH11 : (problem_12_pre_z rows )) (PreH12 : (longest_prefix_z_12 rows i best_idx best )) ,
  (CharPtrArray2.missing_i strings_pre strings_size_pre i row_ptr rows )
  **  (((strings_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
|--
  (CharPtrArray2.full strings_pre strings_size_pre rows )
.

Definition longest_entail_wit_6 := 
forall (strings_size_pre: Z) (strings_pre: Z) (rows: (@list (@list Z))) (i: Z) (len: Z) (best: Z) (best_idx: Z) (PreH1 : (0 <= i)) (PreH2 : (i < strings_size_pre)) (PreH3 : (0 < strings_size_pre)) (PreH4 : (strings_size_pre <= 100)) (PreH5 : (0 <= len)) (PreH6 : (len < INT_MAX)) (PreH7 : (rows_well_formed_12 rows strings_size_pre )) (PreH8 : (problem_12_pre_z rows )) (PreH9 : (longest_prefix_z_12 rows (i + 1 ) best_idx best )) ,
  (CharPtrArray2.full strings_pre strings_size_pre rows )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= strings_size_pre) ” 
  &&  “ (0 < strings_size_pre) ” 
  &&  “ (strings_size_pre <= 100) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (rows_well_formed_12 rows strings_size_pre ) ” 
  &&  “ (problem_12_pre_z rows ) ” 
  &&  “ (longest_prefix_z_12 rows (i + 1 ) best_idx best ) ”
  &&  (CharPtrArray2.full strings_pre strings_size_pre rows )
.

Definition longest_entail_wit_7 := 
(
forall (strings_size_pre: Z) (strings_pre: Z) (rows: (@list (@list Z))) (best_idx: Z) (best: Z) (len: Z) (i: Z) (PreH1 : (i >= strings_size_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= strings_size_pre)) (PreH4 : (0 < strings_size_pre)) (PreH5 : (strings_size_pre <= 100)) (PreH6 : (0 <= len)) (PreH7 : (len < INT_MAX)) (PreH8 : (rows_well_formed_12 rows strings_size_pre )) (PreH9 : (problem_12_pre_z rows )) (PreH10 : (longest_prefix_z_12 rows i best_idx best )) ,
  (CharPtrArray2.full strings_pre strings_size_pre rows )
|--
  EX (row_ptr: Z) ,
  “ (0 < strings_size_pre) ” 
  &&  “ (0 <= best_idx) ” 
  &&  “ (best_idx < strings_size_pre) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (rows_well_formed_12 rows strings_size_pre ) ” 
  &&  “ (problem_12_pre_z rows ) ” 
  &&  “ (longest_prefix_z_12 rows strings_size_pre best_idx best ) ” 
  &&  “ (problem_12_spec_some_z rows best_idx ) ”
  &&  (CharPtrArray2.missing_i strings_pre strings_size_pre best_idx row_ptr rows )
  **  (((strings_pre + (best_idx * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (best_idx) (rows) ((@nil Z))))) (Znth (best_idx) (rows) ((@nil Z))) )
) \/
(
forall (strings_size_pre: Z) (strings_pre: Z) (rows: (@list (@list Z))) (best_idx: Z) (best: Z) (len: Z) (i: Z) (PreH1 : (i >= strings_size_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= strings_size_pre)) (PreH4 : (0 < strings_size_pre)) (PreH5 : (strings_size_pre <= 100)) (PreH6 : (0 <= len)) (PreH7 : (len < INT_MAX)) (PreH8 : (rows_well_formed_12 rows strings_size_pre )) (PreH9 : (problem_12_pre_z rows )) (PreH10 : (longest_prefix_z_12 rows i best_idx best )) ,
  (CharPtrArray2.full strings_pre strings_size_pre rows )
|--
  EX (row_ptr: Z) ,
  “ (0 < strings_size_pre) ” 
  &&  “ (0 <= best_idx) ” 
  &&  “ (best_idx < strings_size_pre) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (rows_well_formed_12 rows strings_size_pre ) ” 
  &&  “ (problem_12_pre_z rows ) ” 
  &&  “ (longest_prefix_z_12 rows strings_size_pre best_idx best ) ” 
  &&  “ (problem_12_spec_some_z rows best_idx ) ”
  &&  (CharPtrArray2.missing_i strings_pre strings_size_pre best_idx row_ptr rows )
  **  (((strings_pre + (best_idx * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (best_idx) (rows) ((@nil Z))))) (Znth (best_idx) (rows) ((@nil Z))) )
).

Definition longest_return_wit_1 := 
forall (strings_size_pre: Z) (strings_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (best_idx_2: Z) (len: Z) (best: Z) (PreH1 : (0 < strings_size_pre)) (PreH2 : (0 <= best_idx_2)) (PreH3 : (best_idx_2 < strings_size_pre)) (PreH4 : (0 <= len)) (PreH5 : (len < INT_MAX)) (PreH6 : (rows_well_formed_12 rows strings_size_pre )) (PreH7 : (problem_12_pre_z rows )) (PreH8 : (longest_prefix_z_12 rows strings_size_pre best_idx_2 best )) (PreH9 : (problem_12_spec_some_z rows best_idx_2 )) ,
  (CharPtrArray2.missing_i strings_pre strings_size_pre best_idx_2 row_ptr rows )
  **  (((strings_pre + (best_idx_2 * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (best_idx_2) (rows) ((@nil Z))))) (Znth (best_idx_2) (rows) ((@nil Z))) )
|--
  (“ (strings_size_pre = 0) ” 
  &&  “ (row_ptr = 0) ” 
  &&  “ (problem_12_spec_none_z rows ) ”
  &&  (CharPtrArray2.full strings_pre strings_size_pre rows ))
  ||
  (EX (row_ptr_2: Z)  (best_idx: Z) ,
  “ (0 < strings_size_pre) ” 
  &&  “ (0 <= best_idx) ” 
  &&  “ (best_idx < strings_size_pre) ” 
  &&  “ (row_ptr = row_ptr_2) ” 
  &&  “ (problem_12_spec_some_z rows best_idx ) ”
  &&  (CharPtrArray2.missing_i strings_pre strings_size_pre best_idx row_ptr_2 rows )
  **  (((strings_pre + (best_idx * sizeof(PTR) ) )) # Ptr  |-> row_ptr_2)
  **  (CharArray.full row_ptr_2 (Zlength ((Znth (best_idx) (rows) ((@nil Z))))) (Znth (best_idx) (rows) ((@nil Z))) ))
.

Definition longest_return_wit_2 := 
forall (strings_size_pre: Z) (strings_pre: Z) (rows: (@list (@list Z))) (PreH1 : (strings_size_pre = 0)) (PreH2 : (0 <= strings_size_pre)) (PreH3 : (strings_size_pre <= 100)) (PreH4 : (rows_well_formed_12 rows strings_size_pre )) (PreH5 : (problem_12_pre_z rows )) ,
  (CharPtrArray2.full strings_pre strings_size_pre rows )
|--
  (“ (strings_size_pre = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (problem_12_spec_none_z rows ) ”
  &&  (CharPtrArray2.full strings_pre strings_size_pre rows ))
  ||
  (EX (row_ptr: Z)  (best_idx: Z) ,
  “ (0 < strings_size_pre) ” 
  &&  “ (0 <= best_idx) ” 
  &&  “ (best_idx < strings_size_pre) ” 
  &&  “ (0 = row_ptr) ” 
  &&  “ (problem_12_spec_some_z rows best_idx ) ”
  &&  (CharPtrArray2.missing_i strings_pre strings_size_pre best_idx row_ptr rows )
  **  (((strings_pre + (best_idx * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (best_idx) (rows) ((@nil Z))))) (Znth (best_idx) (rows) ((@nil Z))) ))
.

Definition longest_partial_solve_wit_1_pure := 
forall (strings_size_pre: Z) (strings_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (i: Z) (len: Z) (best: Z) (best_idx: Z) (PreH1 : (0 <= i)) (PreH2 : (i < strings_size_pre)) (PreH3 : (0 < strings_size_pre)) (PreH4 : (strings_size_pre <= 100)) (PreH5 : (0 <= len)) (PreH6 : (len < INT_MAX)) (PreH7 : (rows_well_formed_12 rows strings_size_pre )) (PreH8 : (problem_12_pre_z rows )) (PreH9 : (longest_prefix_z_12 rows i best_idx best )) (PreH10 : (valid_string (row_payload_z_12 ((Znth (i) (rows) ((@nil Z))))) )) (PreH11 : ((string_length ((row_payload_z_12 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX)) (PreH12 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = ((string_length ((row_payload_z_12 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "strings_size" ) )) # Int  |-> strings_size_pre)
  **  ((( &( "strings" ) )) # Ptr  |-> strings_pre)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "best_idx" ) )) # Int  |-> best_idx)
  **  (CharPtrArray2.missing_i strings_pre strings_size_pre i row_ptr rows )
  **  (((strings_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_12 ((Znth (i) (rows) ((@nil Z))))) )
|--
  “ (valid_string (row_payload_z_12 ((Znth (i) (rows) ((@nil Z))))) ) ” 
  &&  “ ((string_length ((row_payload_z_12 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX) ”
.

Definition longest_partial_solve_wit_1_aux := 
forall (strings_size_pre: Z) (strings_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (i: Z) (len: Z) (best: Z) (best_idx: Z) (PreH1 : (0 <= i)) (PreH2 : (i < strings_size_pre)) (PreH3 : (0 < strings_size_pre)) (PreH4 : (strings_size_pre <= 100)) (PreH5 : (0 <= len)) (PreH6 : (len < INT_MAX)) (PreH7 : (rows_well_formed_12 rows strings_size_pre )) (PreH8 : (problem_12_pre_z rows )) (PreH9 : (longest_prefix_z_12 rows i best_idx best )) (PreH10 : (valid_string (row_payload_z_12 ((Znth (i) (rows) ((@nil Z))))) )) (PreH11 : ((string_length ((row_payload_z_12 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX)) (PreH12 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = ((string_length ((row_payload_z_12 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) ,
  (CharPtrArray2.missing_i strings_pre strings_size_pre i row_ptr rows )
  **  (((strings_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_12 ((Znth (i) (rows) ((@nil Z))))) )
|--
  “ (valid_string (row_payload_z_12 ((Znth (i) (rows) ((@nil Z))))) ) ” 
  &&  “ ((string_length ((row_payload_z_12 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX) ” 
  &&  “ (0 <= ((string_length ((row_payload_z_12 ((Znth (i) (rows) ((@nil Z))))))) + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < strings_size_pre) ” 
  &&  “ (0 < strings_size_pre) ” 
  &&  “ (strings_size_pre <= 100) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (rows_well_formed_12 rows strings_size_pre ) ” 
  &&  “ (problem_12_pre_z rows ) ” 
  &&  “ (longest_prefix_z_12 rows i best_idx best ) ” 
  &&  “ (valid_string (row_payload_z_12 ((Znth (i) (rows) ((@nil Z))))) ) ” 
  &&  “ ((string_length ((row_payload_z_12 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX) ” 
  &&  “ ((Zlength ((Znth (i) (rows) ((@nil Z))))) = ((string_length ((row_payload_z_12 ((Znth (i) (rows) ((@nil Z))))))) + 1 )) ”
  &&  (store_string row_ptr (row_payload_z_12 ((Znth (i) (rows) ((@nil Z))))) )
  **  (CharPtrArray2.missing_i strings_pre strings_size_pre i row_ptr rows )
  **  (((strings_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
.

Definition longest_partial_solve_wit_1 := longest_partial_solve_wit_1_pure -> longest_partial_solve_wit_1_aux.

Module Type VC_Correct.

Include ptr_array2_Strategy_Correct.
Include char_array_Strategy_Correct.
Include string_Strategy_Correct.

Axiom proof_of_longest_safety_wit_1 : longest_safety_wit_1.
Axiom proof_of_longest_safety_wit_2 : longest_safety_wit_2.
Axiom proof_of_longest_safety_wit_3 : longest_safety_wit_3.
Axiom proof_of_longest_safety_wit_4 : longest_safety_wit_4.
Axiom proof_of_longest_safety_wit_5 : longest_safety_wit_5.
Axiom proof_of_longest_safety_wit_6 : longest_safety_wit_6.
Axiom proof_of_longest_safety_wit_7 : longest_safety_wit_7.
Axiom proof_of_longest_safety_wit_8 : longest_safety_wit_8.
Axiom proof_of_longest_safety_wit_9 : longest_safety_wit_9.
Axiom proof_of_longest_safety_wit_10 : longest_safety_wit_10.
Axiom proof_of_longest_entail_wit_1 : longest_entail_wit_1.
Axiom proof_of_longest_entail_wit_2 : longest_entail_wit_2.
Axiom proof_of_longest_entail_wit_3 : longest_entail_wit_3.
Axiom proof_of_longest_entail_wit_4 : longest_entail_wit_4.
Axiom proof_of_longest_entail_wit_5_1 : longest_entail_wit_5_1.
Axiom proof_of_longest_entail_wit_5_2 : longest_entail_wit_5_2.
Axiom proof_of_longest_entail_wit_6 : longest_entail_wit_6.
Axiom proof_of_longest_entail_wit_7 : longest_entail_wit_7.
Axiom proof_of_longest_return_wit_1 : longest_return_wit_1.
Axiom proof_of_longest_return_wit_2 : longest_return_wit_2.
Axiom proof_of_longest_partial_solve_wit_1_pure : longest_partial_solve_wit_1_pure.
Axiom proof_of_longest_partial_solve_wit_1 : longest_partial_solve_wit_1.

End VC_Correct.
