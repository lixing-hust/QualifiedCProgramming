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
Require Import coins_95.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import ptr_array2_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import ptr_array2_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_proof.

(*----- Function check_dict_case -----*)

Definition check_dict_case_safety_wit_1 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (PreH1 : (0 <= dict_size_pre)) (PreH2 : (dict_size_pre <= 100)) (PreH3 : (rows_well_formed_z rows dict_size_pre )) (PreH4 : (problem_95_pre_z rows )) ,
  ((( &( "isupper" ) )) # Int  |->_)
  **  ((( &( "islower" ) )) # Int  |-> 0)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  (CharPtrArray2.full keys_pre dict_size_pre rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition check_dict_case_safety_wit_2 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (PreH1 : (0 <= dict_size_pre)) (PreH2 : (dict_size_pre <= 100)) (PreH3 : (rows_well_formed_z rows dict_size_pre )) (PreH4 : (problem_95_pre_z rows )) ,
  ((( &( "islower" ) )) # Int  |->_)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  (CharPtrArray2.full keys_pre dict_size_pre rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition check_dict_case_safety_wit_3 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (PreH1 : (0 <= dict_size_pre)) (PreH2 : (dict_size_pre <= 100)) (PreH3 : (rows_well_formed_z rows dict_size_pre )) (PreH4 : (problem_95_pre_z rows )) ,
  ((( &( "isupper" ) )) # Int  |-> 0)
  **  ((( &( "islower" ) )) # Int  |-> 0)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  (CharPtrArray2.full keys_pre dict_size_pre rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition check_dict_case_safety_wit_4 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (dict_size: Z) (islower: Z) (isupper: Z) (PreH1 : (dict_size = 0)) (PreH2 : (islower = 0)) (PreH3 : (isupper = 0)) (PreH4 : (rows_well_formed_z rows dict_size_pre )) (PreH5 : (problem_95_spec_z rows 0 )) ,
  ((( &( "dict_size" ) )) # Int  |-> dict_size)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  ((( &( "islower" ) )) # Int  |-> islower)
  **  ((( &( "isupper" ) )) # Int  |-> isupper)
  **  (CharPtrArray2.full keys_pre dict_size_pre rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition check_dict_case_safety_wit_5 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (PreH1 : (dict_size_pre <> 0)) (PreH2 : (0 <= dict_size_pre)) (PreH3 : (dict_size_pre <= 100)) (PreH4 : (rows_well_formed_z rows dict_size_pre )) (PreH5 : (problem_95_pre_z rows )) ,
  ((( &( "k" ) )) # Int  |->_)
  **  ((( &( "isupper" ) )) # Int  |-> 0)
  **  ((( &( "islower" ) )) # Int  |-> 0)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  (CharPtrArray2.full keys_pre dict_size_pre rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition check_dict_case_safety_wit_6 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (k: Z) (isupper: Z) (islower: Z) (PreH1 : (0 <= k)) (PreH2 : (k < dict_size_pre)) (PreH3 : (0 < dict_size_pre)) (PreH4 : (dict_size_pre <= 100)) (PreH5 : (rows_well_formed_z rows dict_size_pre )) (PreH6 : (problem_95_pre_z rows )) (PreH7 : (scan_state_z rows k 0 islower isupper )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  ((( &( "key" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "isupper" ) )) # Int  |-> isupper)
  **  ((( &( "islower" ) )) # Int  |-> islower)
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition check_dict_case_safety_wit_7 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (islower: Z) (isupper: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : (0 <= i)) (PreH2 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH3 : (0 <= k)) (PreH4 : (k < dict_size_pre)) (PreH5 : (0 < dict_size_pre)) (PreH6 : (dict_size_pre <= 100)) (PreH7 : (rows_well_formed_z rows dict_size_pre )) (PreH8 : (problem_95_pre_z rows )) (PreH9 : (scan_state_z rows k i islower isupper )) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  ((( &( "key" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "isupper" ) )) # Int  |-> isupper)
  **  ((( &( "islower" ) )) # Int  |-> islower)
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition check_dict_case_safety_wit_8 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (islower: Z) (isupper: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH2 : (0 <= i)) (PreH3 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH4 : (0 <= k)) (PreH5 : (k < dict_size_pre)) (PreH6 : (0 < dict_size_pre)) (PreH7 : (dict_size_pre <= 100)) (PreH8 : (rows_well_formed_z rows dict_size_pre )) (PreH9 : (problem_95_pre_z rows )) (PreH10 : (scan_state_z rows k i islower isupper )) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  ((( &( "key" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "isupper" ) )) # Int  |-> isupper)
  **  ((( &( "islower" ) )) # Int  |-> islower)
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ (65 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 65) ”
.

Definition check_dict_case_safety_wit_9 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (islower: Z) (isupper: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH3 : (0 <= i)) (PreH4 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH5 : (0 <= k)) (PreH6 : (k < dict_size_pre)) (PreH7 : (0 < dict_size_pre)) (PreH8 : (dict_size_pre <= 100)) (PreH9 : (rows_well_formed_z rows dict_size_pre )) (PreH10 : (problem_95_pre_z rows )) (PreH11 : (scan_state_z rows k i islower isupper )) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  ((( &( "key" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "isupper" ) )) # Int  |-> isupper)
  **  ((( &( "islower" ) )) # Int  |-> islower)
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ (90 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 90) ”
.

Definition check_dict_case_safety_wit_10 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (islower: Z) (isupper: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH4 : (0 <= i)) (PreH5 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH6 : (0 <= k)) (PreH7 : (k < dict_size_pre)) (PreH8 : (0 < dict_size_pre)) (PreH9 : (dict_size_pre <= 100)) (PreH10 : (rows_well_formed_z rows dict_size_pre )) (PreH11 : (problem_95_pre_z rows )) (PreH12 : (scan_state_z rows k i islower isupper )) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  ((( &( "key" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "isupper" ) )) # Int  |-> isupper)
  **  ((( &( "islower" ) )) # Int  |-> islower)
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ (97 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 97) ”
.

Definition check_dict_case_safety_wit_11 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (islower: Z) (isupper: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH4 : (0 <= i)) (PreH5 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH6 : (0 <= k)) (PreH7 : (k < dict_size_pre)) (PreH8 : (0 < dict_size_pre)) (PreH9 : (dict_size_pre <= 100)) (PreH10 : (rows_well_formed_z rows dict_size_pre )) (PreH11 : (problem_95_pre_z rows )) (PreH12 : (scan_state_z rows k i islower isupper )) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  ((( &( "key" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "isupper" ) )) # Int  |-> isupper)
  **  ((( &( "islower" ) )) # Int  |-> islower)
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ (122 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 122) ”
.

Definition check_dict_case_safety_wit_12 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (islower: Z) (isupper: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH5 : (0 <= i)) (PreH6 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH7 : (0 <= k)) (PreH8 : (k < dict_size_pre)) (PreH9 : (0 < dict_size_pre)) (PreH10 : (dict_size_pre <= 100)) (PreH11 : (rows_well_formed_z rows dict_size_pre )) (PreH12 : (problem_95_pre_z rows )) (PreH13 : (scan_state_z rows k i islower isupper )) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  ((( &( "key" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "isupper" ) )) # Int  |-> isupper)
  **  ((( &( "islower" ) )) # Int  |-> islower)
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ (122 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 122) ”
.

Definition check_dict_case_safety_wit_13 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (islower: Z) (isupper: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 122)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH5 : (0 <= i)) (PreH6 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH7 : (0 <= k)) (PreH8 : (k < dict_size_pre)) (PreH9 : (0 < dict_size_pre)) (PreH10 : (dict_size_pre <= 100)) (PreH11 : (rows_well_formed_z rows dict_size_pre )) (PreH12 : (problem_95_pre_z rows )) (PreH13 : (scan_state_z rows k i islower isupper )) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  ((( &( "key" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "isupper" ) )) # Int  |-> isupper)
  **  ((( &( "islower" ) )) # Int  |-> islower)
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ False ”
.

Definition check_dict_case_safety_wit_14 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (islower: Z) (isupper: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) < 97)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH5 : (0 <= i)) (PreH6 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH7 : (0 <= k)) (PreH8 : (k < dict_size_pre)) (PreH9 : (0 < dict_size_pre)) (PreH10 : (dict_size_pre <= 100)) (PreH11 : (rows_well_formed_z rows dict_size_pre )) (PreH12 : (problem_95_pre_z rows )) (PreH13 : (scan_state_z rows k i islower isupper )) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  ((( &( "key" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "isupper" ) )) # Int  |-> isupper)
  **  ((( &( "islower" ) )) # Int  |-> islower)
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition check_dict_case_safety_wit_15 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (islower: Z) (isupper: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) < 65)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH3 : (0 <= i)) (PreH4 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH5 : (0 <= k)) (PreH6 : (k < dict_size_pre)) (PreH7 : (0 < dict_size_pre)) (PreH8 : (dict_size_pre <= 100)) (PreH9 : (rows_well_formed_z rows dict_size_pre )) (PreH10 : (problem_95_pre_z rows )) (PreH11 : (scan_state_z rows k i islower isupper )) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  ((( &( "key" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "isupper" ) )) # Int  |-> isupper)
  **  ((( &( "islower" ) )) # Int  |-> islower)
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition check_dict_case_safety_wit_16 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (islower: Z) (isupper: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 122)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH6 : (0 <= i)) (PreH7 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH8 : (0 <= k)) (PreH9 : (k < dict_size_pre)) (PreH10 : (0 < dict_size_pre)) (PreH11 : (dict_size_pre <= 100)) (PreH12 : (rows_well_formed_z rows dict_size_pre )) (PreH13 : (problem_95_pre_z rows )) (PreH14 : (scan_state_z rows k i islower isupper )) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  ((( &( "key" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "isupper" ) )) # Int  |-> isupper)
  **  ((( &( "islower" ) )) # Int  |-> islower)
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition check_dict_case_safety_wit_17 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (islower: Z) (isupper: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH6 : (0 <= i)) (PreH7 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH8 : (0 <= k)) (PreH9 : (k < dict_size_pre)) (PreH10 : (0 < dict_size_pre)) (PreH11 : (dict_size_pre <= 100)) (PreH12 : (rows_well_formed_z rows dict_size_pre )) (PreH13 : (problem_95_pre_z rows )) (PreH14 : (scan_state_z rows k i islower isupper )) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  ((( &( "key" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "isupper" ) )) # Int  |-> isupper)
  **  ((( &( "islower" ) )) # Int  |-> islower)
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ (65 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 65) ”
.

Definition check_dict_case_safety_wit_18 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (islower: Z) (isupper: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH5 : (0 <= i)) (PreH6 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH7 : (0 <= k)) (PreH8 : (k < dict_size_pre)) (PreH9 : (0 < dict_size_pre)) (PreH10 : (dict_size_pre <= 100)) (PreH11 : (rows_well_formed_z rows dict_size_pre )) (PreH12 : (problem_95_pre_z rows )) (PreH13 : (scan_state_z rows k i islower isupper )) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  ((( &( "key" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "isupper" ) )) # Int  |-> isupper)
  **  ((( &( "islower" ) )) # Int  |-> islower)
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ (65 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 65) ”
.

Definition check_dict_case_safety_wit_19 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (islower: Z) (isupper: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) < 65)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH6 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH7 : (0 <= i)) (PreH8 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH9 : (0 <= k)) (PreH10 : (k < dict_size_pre)) (PreH11 : (0 < dict_size_pre)) (PreH12 : (dict_size_pre <= 100)) (PreH13 : (rows_well_formed_z rows dict_size_pre )) (PreH14 : (problem_95_pre_z rows )) (PreH15 : (scan_state_z rows k i islower isupper )) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  ((( &( "key" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "isupper" ) )) # Int  |-> isupper)
  **  ((( &( "islower" ) )) # Int  |-> islower)
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ False ”
.

Definition check_dict_case_safety_wit_20 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (islower: Z) (isupper: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) < 65)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH6 : (0 <= i)) (PreH7 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH8 : (0 <= k)) (PreH9 : (k < dict_size_pre)) (PreH10 : (0 < dict_size_pre)) (PreH11 : (dict_size_pre <= 100)) (PreH12 : (rows_well_formed_z rows dict_size_pre )) (PreH13 : (problem_95_pre_z rows )) (PreH14 : (scan_state_z rows k i islower isupper )) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  ((( &( "key" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "isupper" ) )) # Int  |-> isupper)
  **  ((( &( "islower" ) )) # Int  |-> islower)
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ False ”
.

Definition check_dict_case_safety_wit_21 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (islower: Z) (isupper: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH6 : (0 <= i)) (PreH7 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH8 : (0 <= k)) (PreH9 : (k < dict_size_pre)) (PreH10 : (0 < dict_size_pre)) (PreH11 : (dict_size_pre <= 100)) (PreH12 : (rows_well_formed_z rows dict_size_pre )) (PreH13 : (problem_95_pre_z rows )) (PreH14 : (scan_state_z rows k i islower isupper )) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  ((( &( "key" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "isupper" ) )) # Int  |-> isupper)
  **  ((( &( "islower" ) )) # Int  |-> islower)
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ (90 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 90) ”
.

Definition check_dict_case_safety_wit_22 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (islower: Z) (isupper: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH6 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH7 : (0 <= i)) (PreH8 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH9 : (0 <= k)) (PreH10 : (k < dict_size_pre)) (PreH11 : (0 < dict_size_pre)) (PreH12 : (dict_size_pre <= 100)) (PreH13 : (rows_well_formed_z rows dict_size_pre )) (PreH14 : (problem_95_pre_z rows )) (PreH15 : (scan_state_z rows k i islower isupper )) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  ((( &( "key" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "isupper" ) )) # Int  |-> isupper)
  **  ((( &( "islower" ) )) # Int  |-> islower)
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ (90 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 90) ”
.

Definition check_dict_case_safety_wit_23 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (islower: Z) (isupper: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH6 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH7 : (0 <= i)) (PreH8 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH9 : (0 <= k)) (PreH10 : (k < dict_size_pre)) (PreH11 : (0 < dict_size_pre)) (PreH12 : (dict_size_pre <= 100)) (PreH13 : (rows_well_formed_z rows dict_size_pre )) (PreH14 : (problem_95_pre_z rows )) (PreH15 : (scan_state_z rows k i islower isupper )) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  ((( &( "key" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "isupper" ) )) # Int  |-> isupper)
  **  ((( &( "islower" ) )) # Int  |-> islower)
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ False ”
.

Definition check_dict_case_safety_wit_24 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (islower: Z) (isupper: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH6 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH7 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH8 : (0 <= i)) (PreH9 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH10 : (0 <= k)) (PreH11 : (k < dict_size_pre)) (PreH12 : (0 < dict_size_pre)) (PreH13 : (dict_size_pre <= 100)) (PreH14 : (rows_well_formed_z rows dict_size_pre )) (PreH15 : (problem_95_pre_z rows )) (PreH16 : (scan_state_z rows k i islower isupper )) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  ((( &( "key" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "isupper" ) )) # Int  |-> isupper)
  **  ((( &( "islower" ) )) # Int  |-> islower)
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ False ”
.

Definition check_dict_case_safety_wit_25 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (islower: Z) (isupper: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH6 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH7 : (0 <= i)) (PreH8 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH9 : (0 <= k)) (PreH10 : (k < dict_size_pre)) (PreH11 : (0 < dict_size_pre)) (PreH12 : (dict_size_pre <= 100)) (PreH13 : (rows_well_formed_z rows dict_size_pre )) (PreH14 : (problem_95_pre_z rows )) (PreH15 : (scan_state_z rows k i islower isupper )) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  ((( &( "key" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "isupper" ) )) # Int  |-> isupper)
  **  ((( &( "islower" ) )) # Int  |-> islower)
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition check_dict_case_safety_wit_26 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (islower: Z) (isupper: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH6 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH7 : (0 <= i)) (PreH8 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH9 : (0 <= k)) (PreH10 : (k < dict_size_pre)) (PreH11 : (0 < dict_size_pre)) (PreH12 : (dict_size_pre <= 100)) (PreH13 : (rows_well_formed_z rows dict_size_pre )) (PreH14 : (problem_95_pre_z rows )) (PreH15 : (scan_state_z rows k i islower isupper )) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  ((( &( "key" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "isupper" ) )) # Int  |-> 1)
  **  ((( &( "islower" ) )) # Int  |-> islower)
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ (97 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 97) ”
.

Definition check_dict_case_safety_wit_27 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (islower: Z) (isupper: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH6 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH7 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH8 : (0 <= i)) (PreH9 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH10 : (0 <= k)) (PreH11 : (k < dict_size_pre)) (PreH12 : (0 < dict_size_pre)) (PreH13 : (dict_size_pre <= 100)) (PreH14 : (rows_well_formed_z rows dict_size_pre )) (PreH15 : (problem_95_pre_z rows )) (PreH16 : (scan_state_z rows k i islower isupper )) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  ((( &( "key" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "isupper" ) )) # Int  |-> isupper)
  **  ((( &( "islower" ) )) # Int  |-> islower)
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ (97 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 97) ”
.

Definition check_dict_case_safety_wit_28 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (islower: Z) (isupper: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90)) (PreH6 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH7 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH8 : (0 <= i)) (PreH9 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH10 : (0 <= k)) (PreH11 : (k < dict_size_pre)) (PreH12 : (0 < dict_size_pre)) (PreH13 : (dict_size_pre <= 100)) (PreH14 : (rows_well_formed_z rows dict_size_pre )) (PreH15 : (problem_95_pre_z rows )) (PreH16 : (scan_state_z rows k i islower isupper )) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  ((( &( "key" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "isupper" ) )) # Int  |-> 1)
  **  ((( &( "islower" ) )) # Int  |-> islower)
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ False ”
.

Definition check_dict_case_safety_wit_29 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (islower: Z) (isupper: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) < 97)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH6 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH7 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH8 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH9 : (0 <= i)) (PreH10 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH11 : (0 <= k)) (PreH12 : (k < dict_size_pre)) (PreH13 : (0 < dict_size_pre)) (PreH14 : (dict_size_pre <= 100)) (PreH15 : (rows_well_formed_z rows dict_size_pre )) (PreH16 : (problem_95_pre_z rows )) (PreH17 : (scan_state_z rows k i islower isupper )) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  ((( &( "key" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "isupper" ) )) # Int  |-> isupper)
  **  ((( &( "islower" ) )) # Int  |-> islower)
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ False ”
.

Definition check_dict_case_safety_wit_30 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (islower: Z) (isupper: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH6 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH7 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH8 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH9 : (0 <= i)) (PreH10 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH11 : (0 <= k)) (PreH12 : (k < dict_size_pre)) (PreH13 : (0 < dict_size_pre)) (PreH14 : (dict_size_pre <= 100)) (PreH15 : (rows_well_formed_z rows dict_size_pre )) (PreH16 : (problem_95_pre_z rows )) (PreH17 : (scan_state_z rows k i islower isupper )) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  ((( &( "key" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "isupper" ) )) # Int  |-> isupper)
  **  ((( &( "islower" ) )) # Int  |-> islower)
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ (122 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 122) ”
.

Definition check_dict_case_safety_wit_31 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (islower: Z) (isupper: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 122)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH6 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH7 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH8 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH9 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH10 : (0 <= i)) (PreH11 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH12 : (0 <= k)) (PreH13 : (k < dict_size_pre)) (PreH14 : (0 < dict_size_pre)) (PreH15 : (dict_size_pre <= 100)) (PreH16 : (rows_well_formed_z rows dict_size_pre )) (PreH17 : (problem_95_pre_z rows )) (PreH18 : (scan_state_z rows k i islower isupper )) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  ((( &( "key" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "isupper" ) )) # Int  |-> isupper)
  **  ((( &( "islower" ) )) # Int  |-> islower)
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ False ”
.

Definition check_dict_case_safety_wit_32 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (islower: Z) (isupper: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH6 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH7 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH8 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH9 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH10 : (0 <= i)) (PreH11 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH12 : (0 <= k)) (PreH13 : (k < dict_size_pre)) (PreH14 : (0 < dict_size_pre)) (PreH15 : (dict_size_pre <= 100)) (PreH16 : (rows_well_formed_z rows dict_size_pre )) (PreH17 : (problem_95_pre_z rows )) (PreH18 : (scan_state_z rows k i islower isupper )) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  ((( &( "key" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "isupper" ) )) # Int  |-> isupper)
  **  ((( &( "islower" ) )) # Int  |-> islower)
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition check_dict_case_safety_wit_33 := 
(
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (islower: Z) (isupper: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) < 97)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90)) (PreH6 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH7 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH8 : (0 <= i)) (PreH9 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH10 : (0 <= k)) (PreH11 : (k < dict_size_pre)) (PreH12 : (0 < dict_size_pre)) (PreH13 : (dict_size_pre <= 100)) (PreH14 : (rows_well_formed_z rows dict_size_pre )) (PreH15 : (problem_95_pre_z rows )) (PreH16 : (scan_state_z rows k i islower isupper )) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  ((( &( "key" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "isupper" ) )) # Int  |-> 1)
  **  ((( &( "islower" ) )) # Int  |-> islower)
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ ((1 + islower ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (1 + islower )) ”
) \/
(
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (islower: Z) (isupper: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) < 97)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90)) (PreH6 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH7 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH8 : (0 <= i)) (PreH9 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH10 : (0 <= k)) (PreH11 : (k < dict_size_pre)) (PreH12 : (0 < dict_size_pre)) (PreH13 : (dict_size_pre <= 100)) (PreH14 : (rows_well_formed_z rows dict_size_pre )) (PreH15 : (problem_95_pre_z rows )) (PreH16 : (scan_state_z rows k i islower isupper )) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  ((( &( "key" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "isupper" ) )) # Int  |-> 1)
  **  ((( &( "islower" ) )) # Int  |-> islower)
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ ((1 + islower ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (1 + islower )) ”
).

Definition check_dict_case_safety_wit_33_split_goal_1 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (islower: Z) (isupper: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) < 97)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90)) (PreH6 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH7 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH8 : (0 <= i)) (PreH9 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH10 : (0 <= k)) (PreH11 : (k < dict_size_pre)) (PreH12 : (0 < dict_size_pre)) (PreH13 : (dict_size_pre <= 100)) (PreH14 : (rows_well_formed_z rows dict_size_pre )) (PreH15 : (problem_95_pre_z rows )) (PreH16 : (scan_state_z rows k i islower isupper )) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  ((( &( "key" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "isupper" ) )) # Int  |-> 1)
  **  ((( &( "islower" ) )) # Int  |-> islower)
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ ((1 + islower ) <= INT_MAX) ”
.

Definition check_dict_case_safety_wit_33_split_goal_2 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (islower: Z) (isupper: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) < 97)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90)) (PreH6 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH7 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH8 : (0 <= i)) (PreH9 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH10 : (0 <= k)) (PreH11 : (k < dict_size_pre)) (PreH12 : (0 < dict_size_pre)) (PreH13 : (dict_size_pre <= 100)) (PreH14 : (rows_well_formed_z rows dict_size_pre )) (PreH15 : (problem_95_pre_z rows )) (PreH16 : (scan_state_z rows k i islower isupper )) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  ((( &( "key" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "isupper" ) )) # Int  |-> 1)
  **  ((( &( "islower" ) )) # Int  |-> islower)
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ ((INT_MIN) <= (1 + islower )) ”
.

Definition check_dict_case_safety_wit_34 := 
(
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (islower: Z) (isupper: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH6 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH7 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH8 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH9 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH10 : (0 <= i)) (PreH11 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH12 : (0 <= k)) (PreH13 : (k < dict_size_pre)) (PreH14 : (0 < dict_size_pre)) (PreH15 : (dict_size_pre <= 100)) (PreH16 : (rows_well_formed_z rows dict_size_pre )) (PreH17 : (problem_95_pre_z rows )) (PreH18 : (scan_state_z rows k i islower isupper )) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  ((( &( "key" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "isupper" ) )) # Int  |-> isupper)
  **  ((( &( "islower" ) )) # Int  |-> 1)
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ ((isupper + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (isupper + 1 )) ”
) \/
(
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (islower: Z) (isupper: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH6 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH7 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH8 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH9 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH10 : (0 <= i)) (PreH11 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH12 : (0 <= k)) (PreH13 : (k < dict_size_pre)) (PreH14 : (0 < dict_size_pre)) (PreH15 : (dict_size_pre <= 100)) (PreH16 : (rows_well_formed_z rows dict_size_pre )) (PreH17 : (problem_95_pre_z rows )) (PreH18 : (scan_state_z rows k i islower isupper )) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  ((( &( "key" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "isupper" ) )) # Int  |-> isupper)
  **  ((( &( "islower" ) )) # Int  |-> 1)
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ ((isupper + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (isupper + 1 )) ”
).

Definition check_dict_case_safety_wit_34_split_goal_1 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (islower: Z) (isupper: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH6 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH7 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH8 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH9 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH10 : (0 <= i)) (PreH11 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH12 : (0 <= k)) (PreH13 : (k < dict_size_pre)) (PreH14 : (0 < dict_size_pre)) (PreH15 : (dict_size_pre <= 100)) (PreH16 : (rows_well_formed_z rows dict_size_pre )) (PreH17 : (problem_95_pre_z rows )) (PreH18 : (scan_state_z rows k i islower isupper )) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  ((( &( "key" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "isupper" ) )) # Int  |-> isupper)
  **  ((( &( "islower" ) )) # Int  |-> 1)
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ ((isupper + 1 ) <= INT_MAX) ”
.

Definition check_dict_case_safety_wit_34_split_goal_2 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (islower: Z) (isupper: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH6 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH7 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH8 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH9 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH10 : (0 <= i)) (PreH11 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH12 : (0 <= k)) (PreH13 : (k < dict_size_pre)) (PreH14 : (0 < dict_size_pre)) (PreH15 : (dict_size_pre <= 100)) (PreH16 : (rows_well_formed_z rows dict_size_pre )) (PreH17 : (problem_95_pre_z rows )) (PreH18 : (scan_state_z rows k i islower isupper )) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  ((( &( "key" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "isupper" ) )) # Int  |-> isupper)
  **  ((( &( "islower" ) )) # Int  |-> 1)
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ ((INT_MIN) <= (isupper + 1 )) ”
.

Definition check_dict_case_safety_wit_35 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (islower: Z) (isupper: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH6 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH7 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH8 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH9 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH10 : (0 <= i)) (PreH11 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH12 : (0 <= k)) (PreH13 : (k < dict_size_pre)) (PreH14 : (0 < dict_size_pre)) (PreH15 : (dict_size_pre <= 100)) (PreH16 : (rows_well_formed_z rows dict_size_pre )) (PreH17 : (problem_95_pre_z rows )) (PreH18 : (scan_state_z rows k i islower isupper )) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  ((( &( "key" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "isupper" ) )) # Int  |-> isupper)
  **  ((( &( "islower" ) )) # Int  |-> 1)
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition check_dict_case_safety_wit_36 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (islower: Z) (isupper: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) < 97)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90)) (PreH6 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH7 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH8 : (0 <= i)) (PreH9 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH10 : (0 <= k)) (PreH11 : (k < dict_size_pre)) (PreH12 : (0 < dict_size_pre)) (PreH13 : (dict_size_pre <= 100)) (PreH14 : (rows_well_formed_z rows dict_size_pre )) (PreH15 : (problem_95_pre_z rows )) (PreH16 : (scan_state_z rows k i islower isupper )) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  ((( &( "key" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "isupper" ) )) # Int  |-> 1)
  **  ((( &( "islower" ) )) # Int  |-> islower)
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition check_dict_case_safety_wit_37 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (islower: Z) (isupper: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((isupper + 1 ) = 2)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH6 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH7 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH8 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH9 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH10 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH11 : (0 <= i)) (PreH12 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH13 : (0 <= k)) (PreH14 : (k < dict_size_pre)) (PreH15 : (0 < dict_size_pre)) (PreH16 : (dict_size_pre <= 100)) (PreH17 : (rows_well_formed_z rows dict_size_pre )) (PreH18 : (problem_95_pre_z rows )) (PreH19 : (scan_state_z rows k i islower isupper )) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  ((( &( "key" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "isupper" ) )) # Int  |-> isupper)
  **  ((( &( "islower" ) )) # Int  |-> 1)
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition check_dict_case_safety_wit_38 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (islower: Z) (isupper: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((1 + islower ) = 2)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) < 97)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH6 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90)) (PreH7 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH8 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH9 : (0 <= i)) (PreH10 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH11 : (0 <= k)) (PreH12 : (k < dict_size_pre)) (PreH13 : (0 < dict_size_pre)) (PreH14 : (dict_size_pre <= 100)) (PreH15 : (rows_well_formed_z rows dict_size_pre )) (PreH16 : (problem_95_pre_z rows )) (PreH17 : (scan_state_z rows k i islower isupper )) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  ((( &( "key" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "isupper" ) )) # Int  |-> 1)
  **  ((( &( "islower" ) )) # Int  |-> islower)
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition check_dict_case_safety_wit_39 := 
(
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (islower: Z) (isupper: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((isupper + 1 ) <> 2)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH6 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH7 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH8 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH9 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH10 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH11 : (0 <= i)) (PreH12 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH13 : (0 <= k)) (PreH14 : (k < dict_size_pre)) (PreH15 : (0 < dict_size_pre)) (PreH16 : (dict_size_pre <= 100)) (PreH17 : (rows_well_formed_z rows dict_size_pre )) (PreH18 : (problem_95_pre_z rows )) (PreH19 : (scan_state_z rows k i islower isupper )) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  ((( &( "key" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "isupper" ) )) # Int  |-> isupper)
  **  ((( &( "islower" ) )) # Int  |-> 1)
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
) \/
(
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (islower: Z) (isupper: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((isupper + 1 ) <> 2)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH6 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH7 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH8 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH9 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH10 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH11 : (0 <= i)) (PreH12 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH13 : (0 <= k)) (PreH14 : (k < dict_size_pre)) (PreH15 : (0 < dict_size_pre)) (PreH16 : (dict_size_pre <= 100)) (PreH17 : (rows_well_formed_z rows dict_size_pre )) (PreH18 : (problem_95_pre_z rows )) (PreH19 : (scan_state_z rows k i islower isupper )) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  ((( &( "key" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "isupper" ) )) # Int  |-> isupper)
  **  ((( &( "islower" ) )) # Int  |-> 1)
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
).

Definition check_dict_case_safety_wit_39_split_goal_1 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (islower: Z) (isupper: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((isupper + 1 ) <> 2)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH6 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH7 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH8 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH9 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH10 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH11 : (0 <= i)) (PreH12 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH13 : (0 <= k)) (PreH14 : (k < dict_size_pre)) (PreH15 : (0 < dict_size_pre)) (PreH16 : (dict_size_pre <= 100)) (PreH17 : (rows_well_formed_z rows dict_size_pre )) (PreH18 : (problem_95_pre_z rows )) (PreH19 : (scan_state_z rows k i islower isupper )) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  ((( &( "key" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "isupper" ) )) # Int  |-> isupper)
  **  ((( &( "islower" ) )) # Int  |-> 1)
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ ((i + 1 ) <= INT_MAX) ”
.

Definition check_dict_case_safety_wit_39_split_goal_2 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (islower: Z) (isupper: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((isupper + 1 ) <> 2)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH6 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH7 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH8 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH9 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH10 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH11 : (0 <= i)) (PreH12 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH13 : (0 <= k)) (PreH14 : (k < dict_size_pre)) (PreH15 : (0 < dict_size_pre)) (PreH16 : (dict_size_pre <= 100)) (PreH17 : (rows_well_formed_z rows dict_size_pre )) (PreH18 : (problem_95_pre_z rows )) (PreH19 : (scan_state_z rows k i islower isupper )) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  ((( &( "key" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "isupper" ) )) # Int  |-> isupper)
  **  ((( &( "islower" ) )) # Int  |-> 1)
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition check_dict_case_safety_wit_40 := 
(
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (islower: Z) (isupper: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((1 + islower ) <> 2)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) < 97)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH6 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90)) (PreH7 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH8 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH9 : (0 <= i)) (PreH10 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH11 : (0 <= k)) (PreH12 : (k < dict_size_pre)) (PreH13 : (0 < dict_size_pre)) (PreH14 : (dict_size_pre <= 100)) (PreH15 : (rows_well_formed_z rows dict_size_pre )) (PreH16 : (problem_95_pre_z rows )) (PreH17 : (scan_state_z rows k i islower isupper )) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  ((( &( "key" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "isupper" ) )) # Int  |-> 1)
  **  ((( &( "islower" ) )) # Int  |-> islower)
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
) \/
(
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (islower: Z) (isupper: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((1 + islower ) <> 2)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) < 97)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH6 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90)) (PreH7 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH8 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH9 : (0 <= i)) (PreH10 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH11 : (0 <= k)) (PreH12 : (k < dict_size_pre)) (PreH13 : (0 < dict_size_pre)) (PreH14 : (dict_size_pre <= 100)) (PreH15 : (rows_well_formed_z rows dict_size_pre )) (PreH16 : (problem_95_pre_z rows )) (PreH17 : (scan_state_z rows k i islower isupper )) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  ((( &( "key" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "isupper" ) )) # Int  |-> 1)
  **  ((( &( "islower" ) )) # Int  |-> islower)
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
).

Definition check_dict_case_safety_wit_40_split_goal_1 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (islower: Z) (isupper: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((1 + islower ) <> 2)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) < 97)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH6 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90)) (PreH7 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH8 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH9 : (0 <= i)) (PreH10 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH11 : (0 <= k)) (PreH12 : (k < dict_size_pre)) (PreH13 : (0 < dict_size_pre)) (PreH14 : (dict_size_pre <= 100)) (PreH15 : (rows_well_formed_z rows dict_size_pre )) (PreH16 : (problem_95_pre_z rows )) (PreH17 : (scan_state_z rows k i islower isupper )) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  ((( &( "key" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "isupper" ) )) # Int  |-> 1)
  **  ((( &( "islower" ) )) # Int  |-> islower)
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ ((i + 1 ) <= INT_MAX) ”
.

Definition check_dict_case_safety_wit_40_split_goal_2 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (islower: Z) (isupper: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((1 + islower ) <> 2)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) < 97)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH6 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90)) (PreH7 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH8 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH9 : (0 <= i)) (PreH10 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH11 : (0 <= k)) (PreH12 : (k < dict_size_pre)) (PreH13 : (0 < dict_size_pre)) (PreH14 : (dict_size_pre <= 100)) (PreH15 : (rows_well_formed_z rows dict_size_pre )) (PreH16 : (problem_95_pre_z rows )) (PreH17 : (scan_state_z rows k i islower isupper )) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  ((( &( "key" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "isupper" ) )) # Int  |-> 1)
  **  ((( &( "islower" ) )) # Int  |-> islower)
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition check_dict_case_safety_wit_41 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (k: Z) (islower: Z) (isupper: Z) (PreH1 : (0 <= k)) (PreH2 : (k < dict_size_pre)) (PreH3 : (0 < dict_size_pre)) (PreH4 : (dict_size_pre <= 100)) (PreH5 : (0 <= islower)) (PreH6 : (islower <= 1)) (PreH7 : (0 <= isupper)) (PreH8 : (isupper <= 1)) (PreH9 : (rows_well_formed_z rows dict_size_pre )) (PreH10 : (problem_95_pre_z rows )) (PreH11 : (scan_state_z rows (k + 1 ) 0 islower isupper )) ,
  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  ((( &( "islower" ) )) # Int  |-> islower)
  **  ((( &( "isupper" ) )) # Int  |-> isupper)
  **  (CharPtrArray2.full keys_pre dict_size_pre rows )
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition check_dict_case_safety_wit_42 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (islower: Z) (isupper: Z) (k: Z) (PreH1 : (k >= dict_size_pre)) (PreH2 : (0 <= k)) (PreH3 : (k <= dict_size_pre)) (PreH4 : (0 < dict_size_pre)) (PreH5 : (dict_size_pre <= 100)) (PreH6 : (rows_well_formed_z rows dict_size_pre )) (PreH7 : (problem_95_pre_z rows )) (PreH8 : (scan_state_z rows k 0 islower isupper )) ,
  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  ((( &( "isupper" ) )) # Int  |-> isupper)
  **  ((( &( "islower" ) )) # Int  |-> islower)
  **  (CharPtrArray2.full keys_pre dict_size_pre rows )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition check_dict_case_entail_wit_1 := 
(
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (PreH1 : (dict_size_pre = 0)) (PreH2 : (0 <= dict_size_pre)) (PreH3 : (dict_size_pre <= 100)) (PreH4 : (rows_well_formed_z rows dict_size_pre )) (PreH5 : (problem_95_pre_z rows )) ,
  (CharPtrArray2.full keys_pre dict_size_pre rows )
|--
  “ (dict_size_pre = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (rows_well_formed_z rows dict_size_pre ) ” 
  &&  “ (problem_95_spec_z rows 0 ) ”
  &&  (CharPtrArray2.full keys_pre dict_size_pre rows )
) \/
(
forall (dict_size_pre: Z) (rows: (@list (@list Z))) (PreH1 : (dict_size_pre = 0)) (PreH2 : (0 <= dict_size_pre)) (PreH3 : (dict_size_pre <= 100)) (PreH4 : (rows_well_formed_z rows dict_size_pre )) (PreH5 : (problem_95_pre_z rows )) ,
  TT && emp 
|--
  “ (problem_95_spec_z rows 0 ) ”
  &&  emp
).

Definition check_dict_case_entail_wit_1_split_goal_1 := 
forall (dict_size_pre: Z) (rows: (@list (@list Z))) (PreH1 : (dict_size_pre = 0)) (PreH2 : (0 <= dict_size_pre)) (PreH3 : (dict_size_pre <= 100)) (PreH4 : (rows_well_formed_z rows dict_size_pre )) (PreH5 : (problem_95_pre_z rows )) ,
  TT && emp 
|--
  “ (problem_95_spec_z rows 0 ) ”
.

Definition check_dict_case_entail_wit_2 := 
(
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (PreH1 : (dict_size_pre <> 0)) (PreH2 : (0 <= dict_size_pre)) (PreH3 : (dict_size_pre <= 100)) (PreH4 : (rows_well_formed_z rows dict_size_pre )) (PreH5 : (problem_95_pre_z rows )) ,
  (CharPtrArray2.full keys_pre dict_size_pre rows )
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= dict_size_pre) ” 
  &&  “ (0 < dict_size_pre) ” 
  &&  “ (dict_size_pre <= 100) ” 
  &&  “ (rows_well_formed_z rows dict_size_pre ) ” 
  &&  “ (problem_95_pre_z rows ) ” 
  &&  “ (scan_state_z rows 0 0 0 0 ) ”
  &&  (CharPtrArray2.full keys_pre dict_size_pre rows )
) \/
(
forall (dict_size_pre: Z) (rows: (@list (@list Z))) (PreH1 : (dict_size_pre <> 0)) (PreH2 : (0 <= dict_size_pre)) (PreH3 : (dict_size_pre <= 100)) (PreH4 : (rows_well_formed_z rows dict_size_pre )) (PreH5 : (problem_95_pre_z rows )) ,
  TT && emp 
|--
  “ (scan_state_z rows 0 0 0 0 ) ”
  &&  emp
).

Definition check_dict_case_entail_wit_2_split_goal_1 := 
forall (dict_size_pre: Z) (rows: (@list (@list Z))) (PreH1 : (dict_size_pre <> 0)) (PreH2 : (0 <= dict_size_pre)) (PreH3 : (dict_size_pre <= 100)) (PreH4 : (rows_well_formed_z rows dict_size_pre )) (PreH5 : (problem_95_pre_z rows )) ,
  TT && emp 
|--
  “ (scan_state_z rows 0 0 0 0 ) ”
.

Definition check_dict_case_entail_wit_3 := 
(
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (islower: Z) (isupper: Z) (k: Z) (PreH1 : (k < dict_size_pre)) (PreH2 : (0 <= k)) (PreH3 : (k <= dict_size_pre)) (PreH4 : (0 < dict_size_pre)) (PreH5 : (dict_size_pre <= 100)) (PreH6 : (rows_well_formed_z rows dict_size_pre )) (PreH7 : (problem_95_pre_z rows )) (PreH8 : (scan_state_z rows k 0 islower isupper )) ,
  (CharPtrArray2.full keys_pre dict_size_pre rows )
|--
  EX (row_ptr: Z) ,
  “ (0 <= k) ” 
  &&  “ (k < dict_size_pre) ” 
  &&  “ (0 < dict_size_pre) ” 
  &&  “ (dict_size_pre <= 100) ” 
  &&  “ (rows_well_formed_z rows dict_size_pre ) ” 
  &&  “ (problem_95_pre_z rows ) ” 
  &&  “ (scan_state_z rows k 0 islower isupper ) ”
  &&  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
) \/
(
forall (dict_size_pre: Z) (rows: (@list (@list Z))) (islower: Z) (isupper: Z) (k: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (0 <= (Zlength ((Znth k rows __default__List_Z))))) (PreH2 : (k < dict_size_pre)) (PreH3 : (0 <= k)) (PreH4 : (k <= dict_size_pre)) (PreH5 : (0 < dict_size_pre)) (PreH6 : (dict_size_pre <= 100)) (PreH7 : (rows_well_formed_z rows dict_size_pre )) (PreH8 : (problem_95_pre_z rows )) (PreH9 : (scan_state_z rows k 0 islower isupper )) ,
  (CharArray.full row_ptr_2 (Zlength ((Znth k rows __default__List_Z))) (Znth k rows __default__List_Z) )
|--
  (CharArray.full row_ptr_2 (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
).

Definition check_dict_case_entail_wit_3_split_goal_spatial := 
forall (dict_size_pre: Z) (rows: (@list (@list Z))) (islower: Z) (isupper: Z) (k: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (0 <= (Zlength ((Znth k rows __default__List_Z))))) (PreH2 : (k < dict_size_pre)) (PreH3 : (0 <= k)) (PreH4 : (k <= dict_size_pre)) (PreH5 : (0 < dict_size_pre)) (PreH6 : (dict_size_pre <= 100)) (PreH7 : (rows_well_formed_z rows dict_size_pre )) (PreH8 : (problem_95_pre_z rows )) (PreH9 : (scan_state_z rows k 0 islower isupper )) ,
  (CharArray.full row_ptr_2 (Zlength ((Znth k rows __default__List_Z))) (Znth k rows __default__List_Z) )
|--
  (CharArray.full row_ptr_2 (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
.

Definition check_dict_case_entail_wit_4 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (k: Z) (isupper: Z) (islower: Z) (PreH1 : (0 <= k)) (PreH2 : (k < dict_size_pre)) (PreH3 : (0 < dict_size_pre)) (PreH4 : (dict_size_pre <= 100)) (PreH5 : (rows_well_formed_z rows dict_size_pre )) (PreH6 : (problem_95_pre_z rows )) (PreH7 : (scan_state_z rows k 0 islower isupper )) ,
  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
|--
  “ (0 <= k) ” 
  &&  “ (k < dict_size_pre) ” 
  &&  “ (0 < dict_size_pre) ” 
  &&  “ (dict_size_pre <= 100) ” 
  &&  “ (rows_well_formed_z rows dict_size_pre ) ” 
  &&  “ (problem_95_pre_z rows ) ” 
  &&  “ (scan_state_z rows k 0 islower isupper ) ”
  &&  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
.

Definition check_dict_case_entail_wit_5 := 
(
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (k: Z) (isupper: Z) (islower: Z) (PreH1 : (0 <= k)) (PreH2 : (k < dict_size_pre)) (PreH3 : (0 < dict_size_pre)) (PreH4 : (dict_size_pre <= 100)) (PreH5 : (rows_well_formed_z rows dict_size_pre )) (PreH6 : (problem_95_pre_z rows )) (PreH7 : (scan_state_z rows k 0 islower isupper )) ,
  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
|--
  “ (0 <= 0) ” 
  &&  “ (0 < (Zlength ((Znth (k) (rows) ((@nil Z)))))) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < dict_size_pre) ” 
  &&  “ (0 < dict_size_pre) ” 
  &&  “ (dict_size_pre <= 100) ” 
  &&  “ (rows_well_formed_z rows dict_size_pre ) ” 
  &&  “ (problem_95_pre_z rows ) ” 
  &&  “ (scan_state_z rows k 0 islower isupper ) ”
  &&  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
) \/
(
forall (dict_size_pre: Z) (rows: (@list (@list Z))) (k: Z) (isupper: Z) (islower: Z) (PreH1 : (0 <= k)) (PreH2 : (k < dict_size_pre)) (PreH3 : (0 < dict_size_pre)) (PreH4 : (dict_size_pre <= 100)) (PreH5 : (rows_well_formed_z rows dict_size_pre )) (PreH6 : (problem_95_pre_z rows )) (PreH7 : (scan_state_z rows k 0 islower isupper )) ,
  TT && emp 
|--
  “ (0 < (Zlength ((Znth (k) (rows) ((@nil Z)))))) ”
  &&  emp
).

Definition check_dict_case_entail_wit_5_split_goal_1 := 
forall (dict_size_pre: Z) (rows: (@list (@list Z))) (k: Z) (isupper: Z) (islower: Z) (PreH1 : (0 <= k)) (PreH2 : (k < dict_size_pre)) (PreH3 : (0 < dict_size_pre)) (PreH4 : (dict_size_pre <= 100)) (PreH5 : (rows_well_formed_z rows dict_size_pre )) (PreH6 : (problem_95_pre_z rows )) (PreH7 : (scan_state_z rows k 0 islower isupper )) ,
  TT && emp 
|--
  “ (0 < (Zlength ((Znth (k) (rows) ((@nil Z)))))) ”
.

Definition check_dict_case_entail_wit_6_1 := 
(
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (islower: Z) (isupper: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((isupper + 1 ) <> 2)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH6 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH7 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH8 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH9 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH10 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH11 : (0 <= i)) (PreH12 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH13 : (0 <= k)) (PreH14 : (k < dict_size_pre)) (PreH15 : (0 < dict_size_pre)) (PreH16 : (dict_size_pre <= 100)) (PreH17 : (rows_well_formed_z rows dict_size_pre )) (PreH18 : (problem_95_pre_z rows )) (PreH19 : (scan_state_z rows k i islower isupper )) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) < (Zlength ((Znth (k) (rows) ((@nil Z)))))) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < dict_size_pre) ” 
  &&  “ (0 < dict_size_pre) ” 
  &&  “ (dict_size_pre <= 100) ” 
  &&  “ (rows_well_formed_z rows dict_size_pre ) ” 
  &&  “ (problem_95_pre_z rows ) ” 
  &&  “ (scan_state_z rows k (i + 1 ) 1 isupper ) ”
  &&  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
) \/
(
forall (dict_size_pre: Z) (rows: (@list (@list Z))) (islower: Z) (isupper: Z) (k: Z) (i: Z) (PreH1 : ((isupper + 1 ) <> 2)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH6 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH7 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH8 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH9 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH10 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH11 : (0 <= i)) (PreH12 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH13 : (0 <= k)) (PreH14 : (k < dict_size_pre)) (PreH15 : (0 < dict_size_pre)) (PreH16 : (dict_size_pre <= 100)) (PreH17 : (rows_well_formed_z rows dict_size_pre )) (PreH18 : (problem_95_pre_z rows )) (PreH19 : (scan_state_z rows k i islower isupper )) ,
  TT && emp 
|--
  “ (scan_state_z rows k (i + 1 ) 1 isupper ) ” 
  &&  “ ((i + 1 ) < (Zlength ((Znth (k) (rows) ((@nil Z)))))) ”
  &&  emp
).

Definition check_dict_case_entail_wit_6_1_split_goal_1 := 
forall (dict_size_pre: Z) (rows: (@list (@list Z))) (islower: Z) (isupper: Z) (k: Z) (i: Z) (PreH1 : ((isupper + 1 ) <> 2)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH6 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH7 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH8 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH9 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH10 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH11 : (0 <= i)) (PreH12 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH13 : (0 <= k)) (PreH14 : (k < dict_size_pre)) (PreH15 : (0 < dict_size_pre)) (PreH16 : (dict_size_pre <= 100)) (PreH17 : (rows_well_formed_z rows dict_size_pre )) (PreH18 : (problem_95_pre_z rows )) (PreH19 : (scan_state_z rows k i islower isupper )) ,
  TT && emp 
|--
  “ (scan_state_z rows k (i + 1 ) 1 isupper ) ”
.

Definition check_dict_case_entail_wit_6_1_split_goal_2 := 
forall (dict_size_pre: Z) (rows: (@list (@list Z))) (islower: Z) (isupper: Z) (k: Z) (i: Z) (PreH1 : ((isupper + 1 ) <> 2)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH6 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH7 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH8 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH9 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH10 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH11 : (0 <= i)) (PreH12 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH13 : (0 <= k)) (PreH14 : (k < dict_size_pre)) (PreH15 : (0 < dict_size_pre)) (PreH16 : (dict_size_pre <= 100)) (PreH17 : (rows_well_formed_z rows dict_size_pre )) (PreH18 : (problem_95_pre_z rows )) (PreH19 : (scan_state_z rows k i islower isupper )) ,
  TT && emp 
|--
  “ ((i + 1 ) < (Zlength ((Znth (k) (rows) ((@nil Z)))))) ”
.

Definition check_dict_case_entail_wit_6_2 := 
(
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (islower: Z) (isupper: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((1 + islower ) <> 2)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) < 97)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH6 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90)) (PreH7 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH8 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH9 : (0 <= i)) (PreH10 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH11 : (0 <= k)) (PreH12 : (k < dict_size_pre)) (PreH13 : (0 < dict_size_pre)) (PreH14 : (dict_size_pre <= 100)) (PreH15 : (rows_well_formed_z rows dict_size_pre )) (PreH16 : (problem_95_pre_z rows )) (PreH17 : (scan_state_z rows k i islower isupper )) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) < (Zlength ((Znth (k) (rows) ((@nil Z)))))) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < dict_size_pre) ” 
  &&  “ (0 < dict_size_pre) ” 
  &&  “ (dict_size_pre <= 100) ” 
  &&  “ (rows_well_formed_z rows dict_size_pre ) ” 
  &&  “ (problem_95_pre_z rows ) ” 
  &&  “ (scan_state_z rows k (i + 1 ) islower 1 ) ”
  &&  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
) \/
(
forall (dict_size_pre: Z) (rows: (@list (@list Z))) (islower: Z) (isupper: Z) (k: Z) (i: Z) (PreH1 : ((1 + islower ) <> 2)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) < 97)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH6 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90)) (PreH7 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH8 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH9 : (0 <= i)) (PreH10 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH11 : (0 <= k)) (PreH12 : (k < dict_size_pre)) (PreH13 : (0 < dict_size_pre)) (PreH14 : (dict_size_pre <= 100)) (PreH15 : (rows_well_formed_z rows dict_size_pre )) (PreH16 : (problem_95_pre_z rows )) (PreH17 : (scan_state_z rows k i islower isupper )) ,
  TT && emp 
|--
  “ (scan_state_z rows k (i + 1 ) islower 1 ) ” 
  &&  “ ((i + 1 ) < (Zlength ((Znth (k) (rows) ((@nil Z)))))) ”
  &&  emp
).

Definition check_dict_case_entail_wit_6_2_split_goal_1 := 
forall (dict_size_pre: Z) (rows: (@list (@list Z))) (islower: Z) (isupper: Z) (k: Z) (i: Z) (PreH1 : ((1 + islower ) <> 2)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) < 97)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH6 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90)) (PreH7 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH8 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH9 : (0 <= i)) (PreH10 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH11 : (0 <= k)) (PreH12 : (k < dict_size_pre)) (PreH13 : (0 < dict_size_pre)) (PreH14 : (dict_size_pre <= 100)) (PreH15 : (rows_well_formed_z rows dict_size_pre )) (PreH16 : (problem_95_pre_z rows )) (PreH17 : (scan_state_z rows k i islower isupper )) ,
  TT && emp 
|--
  “ (scan_state_z rows k (i + 1 ) islower 1 ) ”
.

Definition check_dict_case_entail_wit_6_2_split_goal_2 := 
forall (dict_size_pre: Z) (rows: (@list (@list Z))) (islower: Z) (isupper: Z) (k: Z) (i: Z) (PreH1 : ((1 + islower ) <> 2)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) < 97)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH6 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90)) (PreH7 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH8 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH9 : (0 <= i)) (PreH10 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH11 : (0 <= k)) (PreH12 : (k < dict_size_pre)) (PreH13 : (0 < dict_size_pre)) (PreH14 : (dict_size_pre <= 100)) (PreH15 : (rows_well_formed_z rows dict_size_pre )) (PreH16 : (problem_95_pre_z rows )) (PreH17 : (scan_state_z rows k i islower isupper )) ,
  TT && emp 
|--
  “ ((i + 1 ) < (Zlength ((Znth (k) (rows) ((@nil Z)))))) ”
.

Definition check_dict_case_entail_wit_7 := 
(
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (islower: Z) (isupper: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) = 0)) (PreH2 : (0 <= i)) (PreH3 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH4 : (0 <= k)) (PreH5 : (k < dict_size_pre)) (PreH6 : (0 < dict_size_pre)) (PreH7 : (dict_size_pre <= 100)) (PreH8 : (rows_well_formed_z rows dict_size_pre )) (PreH9 : (problem_95_pre_z rows )) (PreH10 : (scan_state_z rows k i islower isupper )) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ (0 <= k) ” 
  &&  “ (k < dict_size_pre) ” 
  &&  “ (0 < dict_size_pre) ” 
  &&  “ (dict_size_pre <= 100) ” 
  &&  “ (0 <= islower) ” 
  &&  “ (islower <= 1) ” 
  &&  “ (0 <= isupper) ” 
  &&  “ (isupper <= 1) ” 
  &&  “ (rows_well_formed_z rows dict_size_pre ) ” 
  &&  “ (problem_95_pre_z rows ) ” 
  &&  “ (scan_state_z rows (k + 1 ) 0 islower isupper ) ”
  &&  (CharPtrArray2.full keys_pre dict_size_pre rows )
) \/
(
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (islower: Z) (isupper: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : (0 <= (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) = 0)) (PreH3 : (0 <= i)) (PreH4 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH5 : (0 <= k)) (PreH6 : (k < dict_size_pre)) (PreH7 : (0 < dict_size_pre)) (PreH8 : (dict_size_pre <= 100)) (PreH9 : (rows_well_formed_z rows dict_size_pre )) (PreH10 : (problem_95_pre_z rows )) (PreH11 : (scan_state_z rows k i islower isupper )) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ (scan_state_z rows (k + 1 ) 0 islower isupper ) ” 
  &&  “ (isupper <= 1) ” 
  &&  “ (0 <= isupper) ” 
  &&  “ (islower <= 1) ” 
  &&  “ (0 <= islower) ”
  &&  (CharPtrArray2.full keys_pre dict_size_pre rows )
).

Definition check_dict_case_entail_wit_7_split_goal_1 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (islower: Z) (isupper: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : (0 <= (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) = 0)) (PreH3 : (0 <= i)) (PreH4 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH5 : (0 <= k)) (PreH6 : (k < dict_size_pre)) (PreH7 : (0 < dict_size_pre)) (PreH8 : (dict_size_pre <= 100)) (PreH9 : (rows_well_formed_z rows dict_size_pre )) (PreH10 : (problem_95_pre_z rows )) (PreH11 : (scan_state_z rows k i islower isupper )) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ (scan_state_z rows (k + 1 ) 0 islower isupper ) ”
.

Definition check_dict_case_entail_wit_7_split_goal_2 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (islower: Z) (isupper: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : (0 <= (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) = 0)) (PreH3 : (0 <= i)) (PreH4 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH5 : (0 <= k)) (PreH6 : (k < dict_size_pre)) (PreH7 : (0 < dict_size_pre)) (PreH8 : (dict_size_pre <= 100)) (PreH9 : (rows_well_formed_z rows dict_size_pre )) (PreH10 : (problem_95_pre_z rows )) (PreH11 : (scan_state_z rows k i islower isupper )) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ (isupper <= 1) ”
.

Definition check_dict_case_entail_wit_7_split_goal_3 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (islower: Z) (isupper: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : (0 <= (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) = 0)) (PreH3 : (0 <= i)) (PreH4 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH5 : (0 <= k)) (PreH6 : (k < dict_size_pre)) (PreH7 : (0 < dict_size_pre)) (PreH8 : (dict_size_pre <= 100)) (PreH9 : (rows_well_formed_z rows dict_size_pre )) (PreH10 : (problem_95_pre_z rows )) (PreH11 : (scan_state_z rows k i islower isupper )) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ (0 <= isupper) ”
.

Definition check_dict_case_entail_wit_7_split_goal_4 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (islower: Z) (isupper: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : (0 <= (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) = 0)) (PreH3 : (0 <= i)) (PreH4 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH5 : (0 <= k)) (PreH6 : (k < dict_size_pre)) (PreH7 : (0 < dict_size_pre)) (PreH8 : (dict_size_pre <= 100)) (PreH9 : (rows_well_formed_z rows dict_size_pre )) (PreH10 : (problem_95_pre_z rows )) (PreH11 : (scan_state_z rows k i islower isupper )) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ (islower <= 1) ”
.

Definition check_dict_case_entail_wit_7_split_goal_5 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (islower: Z) (isupper: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : (0 <= (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) = 0)) (PreH3 : (0 <= i)) (PreH4 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH5 : (0 <= k)) (PreH6 : (k < dict_size_pre)) (PreH7 : (0 < dict_size_pre)) (PreH8 : (dict_size_pre <= 100)) (PreH9 : (rows_well_formed_z rows dict_size_pre )) (PreH10 : (problem_95_pre_z rows )) (PreH11 : (scan_state_z rows k i islower isupper )) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ (0 <= islower) ”
.

Definition check_dict_case_entail_wit_7_split_goal_spatial := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (islower: Z) (isupper: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : (0 <= (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) = 0)) (PreH3 : (0 <= i)) (PreH4 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH5 : (0 <= k)) (PreH6 : (k < dict_size_pre)) (PreH7 : (0 < dict_size_pre)) (PreH8 : (dict_size_pre <= 100)) (PreH9 : (rows_well_formed_z rows dict_size_pre )) (PreH10 : (problem_95_pre_z rows )) (PreH11 : (scan_state_z rows k i islower isupper )) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  (CharPtrArray2.full keys_pre dict_size_pre rows )
.

Definition check_dict_case_entail_wit_8 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (k: Z) (islower: Z) (isupper: Z) (PreH1 : (0 <= k)) (PreH2 : (k < dict_size_pre)) (PreH3 : (0 < dict_size_pre)) (PreH4 : (dict_size_pre <= 100)) (PreH5 : (0 <= islower)) (PreH6 : (islower <= 1)) (PreH7 : (0 <= isupper)) (PreH8 : (isupper <= 1)) (PreH9 : (rows_well_formed_z rows dict_size_pre )) (PreH10 : (problem_95_pre_z rows )) (PreH11 : (scan_state_z rows (k + 1 ) 0 islower isupper )) ,
  (CharPtrArray2.full keys_pre dict_size_pre rows )
|--
  “ (0 <= (k + 1 )) ” 
  &&  “ ((k + 1 ) <= dict_size_pre) ” 
  &&  “ (0 < dict_size_pre) ” 
  &&  “ (dict_size_pre <= 100) ” 
  &&  “ (rows_well_formed_z rows dict_size_pre ) ” 
  &&  “ (problem_95_pre_z rows ) ” 
  &&  “ (scan_state_z rows (k + 1 ) 0 islower isupper ) ”
  &&  (CharPtrArray2.full keys_pre dict_size_pre rows )
.

Definition check_dict_case_return_wit_1 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (islower: Z) (isupper: Z) (k: Z) (PreH1 : (k >= dict_size_pre)) (PreH2 : (0 <= k)) (PreH3 : (k <= dict_size_pre)) (PreH4 : (0 < dict_size_pre)) (PreH5 : (dict_size_pre <= 100)) (PreH6 : (rows_well_formed_z rows dict_size_pre )) (PreH7 : (problem_95_pre_z rows )) (PreH8 : (scan_state_z rows k 0 islower isupper )) ,
  (CharPtrArray2.full keys_pre dict_size_pre rows )
|--
  (“ (1 = 0) ” 
  &&  “ (problem_95_spec_z rows 1 ) ”
  &&  (CharPtrArray2.full keys_pre dict_size_pre rows ))
  ||
  (“ (1 = 1) ” 
  &&  “ (problem_95_spec_z rows 1 ) ”
  &&  (CharPtrArray2.full keys_pre dict_size_pre rows ))
.

Definition check_dict_case_return_wit_2 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (islower: Z) (isupper: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((isupper + 1 ) = 2)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH6 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH7 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH8 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH9 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH10 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH11 : (0 <= i)) (PreH12 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH13 : (0 <= k)) (PreH14 : (k < dict_size_pre)) (PreH15 : (0 < dict_size_pre)) (PreH16 : (dict_size_pre <= 100)) (PreH17 : (rows_well_formed_z rows dict_size_pre )) (PreH18 : (problem_95_pre_z rows )) (PreH19 : (scan_state_z rows k i islower isupper )) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  (“ (0 = 0) ” 
  &&  “ (problem_95_spec_z rows 0 ) ”
  &&  (CharPtrArray2.full keys_pre dict_size_pre rows ))
  ||
  (“ (0 = 1) ” 
  &&  “ (problem_95_spec_z rows 0 ) ”
  &&  (CharPtrArray2.full keys_pre dict_size_pre rows ))
.

Definition check_dict_case_return_wit_3 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (islower: Z) (isupper: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((1 + islower ) = 2)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) < 97)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH6 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90)) (PreH7 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH8 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH9 : (0 <= i)) (PreH10 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH11 : (0 <= k)) (PreH12 : (k < dict_size_pre)) (PreH13 : (0 < dict_size_pre)) (PreH14 : (dict_size_pre <= 100)) (PreH15 : (rows_well_formed_z rows dict_size_pre )) (PreH16 : (problem_95_pre_z rows )) (PreH17 : (scan_state_z rows k i islower isupper )) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  (“ (0 = 0) ” 
  &&  “ (problem_95_spec_z rows 0 ) ”
  &&  (CharPtrArray2.full keys_pre dict_size_pre rows ))
  ||
  (“ (0 = 1) ” 
  &&  “ (problem_95_spec_z rows 0 ) ”
  &&  (CharPtrArray2.full keys_pre dict_size_pre rows ))
.

Definition check_dict_case_return_wit_4 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (islower: Z) (isupper: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) < 97)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH5 : (0 <= i)) (PreH6 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH7 : (0 <= k)) (PreH8 : (k < dict_size_pre)) (PreH9 : (0 < dict_size_pre)) (PreH10 : (dict_size_pre <= 100)) (PreH11 : (rows_well_formed_z rows dict_size_pre )) (PreH12 : (problem_95_pre_z rows )) (PreH13 : (scan_state_z rows k i islower isupper )) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  (“ (0 = 0) ” 
  &&  “ (problem_95_spec_z rows 0 ) ”
  &&  (CharPtrArray2.full keys_pre dict_size_pre rows ))
  ||
  (“ (0 = 1) ” 
  &&  “ (problem_95_spec_z rows 0 ) ”
  &&  (CharPtrArray2.full keys_pre dict_size_pre rows ))
.

Definition check_dict_case_return_wit_5 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (islower: Z) (isupper: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) < 65)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH3 : (0 <= i)) (PreH4 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH5 : (0 <= k)) (PreH6 : (k < dict_size_pre)) (PreH7 : (0 < dict_size_pre)) (PreH8 : (dict_size_pre <= 100)) (PreH9 : (rows_well_formed_z rows dict_size_pre )) (PreH10 : (problem_95_pre_z rows )) (PreH11 : (scan_state_z rows k i islower isupper )) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  (“ (0 = 0) ” 
  &&  “ (problem_95_spec_z rows 0 ) ”
  &&  (CharPtrArray2.full keys_pre dict_size_pre rows ))
  ||
  (“ (0 = 1) ” 
  &&  “ (problem_95_spec_z rows 0 ) ”
  &&  (CharPtrArray2.full keys_pre dict_size_pre rows ))
.

Definition check_dict_case_return_wit_6 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (islower: Z) (isupper: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 122)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH6 : (0 <= i)) (PreH7 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH8 : (0 <= k)) (PreH9 : (k < dict_size_pre)) (PreH10 : (0 < dict_size_pre)) (PreH11 : (dict_size_pre <= 100)) (PreH12 : (rows_well_formed_z rows dict_size_pre )) (PreH13 : (problem_95_pre_z rows )) (PreH14 : (scan_state_z rows k i islower isupper )) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  (“ (0 = 0) ” 
  &&  “ (problem_95_spec_z rows 0 ) ”
  &&  (CharPtrArray2.full keys_pre dict_size_pre rows ))
  ||
  (“ (0 = 1) ” 
  &&  “ (problem_95_spec_z rows 0 ) ”
  &&  (CharPtrArray2.full keys_pre dict_size_pre rows ))
.

Definition check_dict_case_return_wit_7 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (dict_size: Z) (islower: Z) (isupper: Z) (PreH1 : (dict_size = 0)) (PreH2 : (islower = 0)) (PreH3 : (isupper = 0)) (PreH4 : (rows_well_formed_z rows dict_size_pre )) (PreH5 : (problem_95_spec_z rows 0 )) ,
  (CharPtrArray2.full keys_pre dict_size_pre rows )
|--
  (“ (0 = 0) ” 
  &&  “ (problem_95_spec_z rows 0 ) ”
  &&  (CharPtrArray2.full keys_pre dict_size_pre rows ))
  ||
  (“ (0 = 1) ” 
  &&  “ (problem_95_spec_z rows 0 ) ”
  &&  (CharPtrArray2.full keys_pre dict_size_pre rows ))
.

Definition check_dict_case_partial_solve_wit_1 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (islower: Z) (isupper: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : (0 <= i)) (PreH2 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH3 : (0 <= k)) (PreH4 : (k < dict_size_pre)) (PreH5 : (0 < dict_size_pre)) (PreH6 : (dict_size_pre <= 100)) (PreH7 : (rows_well_formed_z rows dict_size_pre )) (PreH8 : (problem_95_pre_z rows )) (PreH9 : (scan_state_z rows k i islower isupper )) ,
  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
|--
  “ (0 <= i) ” 
  &&  “ (i < (Zlength ((Znth (k) (rows) ((@nil Z)))))) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < dict_size_pre) ” 
  &&  “ (0 < dict_size_pre) ” 
  &&  “ (dict_size_pre <= 100) ” 
  &&  “ (rows_well_formed_z rows dict_size_pre ) ” 
  &&  “ (problem_95_pre_z rows ) ” 
  &&  “ (scan_state_z rows k i islower isupper ) ”
  &&  (((row_ptr + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (Znth (k) (rows) ((@nil Z))) 0))
  **  (CharArray.missing_i row_ptr i 0 (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
.

Definition check_dict_case_partial_solve_wit_2 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (islower: Z) (isupper: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH2 : (0 <= i)) (PreH3 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH4 : (0 <= k)) (PreH5 : (k < dict_size_pre)) (PreH6 : (0 < dict_size_pre)) (PreH7 : (dict_size_pre <= 100)) (PreH8 : (rows_well_formed_z rows dict_size_pre )) (PreH9 : (problem_95_pre_z rows )) (PreH10 : (scan_state_z rows k i islower isupper )) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < (Zlength ((Znth (k) (rows) ((@nil Z)))))) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < dict_size_pre) ” 
  &&  “ (0 < dict_size_pre) ” 
  &&  “ (dict_size_pre <= 100) ” 
  &&  “ (rows_well_formed_z rows dict_size_pre ) ” 
  &&  “ (problem_95_pre_z rows ) ” 
  &&  “ (scan_state_z rows k i islower isupper ) ”
  &&  (((row_ptr + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (Znth (k) (rows) ((@nil Z))) 0))
  **  (CharArray.missing_i row_ptr i 0 (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
.

Definition check_dict_case_partial_solve_wit_3 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (islower: Z) (isupper: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH3 : (0 <= i)) (PreH4 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH5 : (0 <= k)) (PreH6 : (k < dict_size_pre)) (PreH7 : (0 < dict_size_pre)) (PreH8 : (dict_size_pre <= 100)) (PreH9 : (rows_well_formed_z rows dict_size_pre )) (PreH10 : (problem_95_pre_z rows )) (PreH11 : (scan_state_z rows k i islower isupper )) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65) ” 
  &&  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < (Zlength ((Znth (k) (rows) ((@nil Z)))))) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < dict_size_pre) ” 
  &&  “ (0 < dict_size_pre) ” 
  &&  “ (dict_size_pre <= 100) ” 
  &&  “ (rows_well_formed_z rows dict_size_pre ) ” 
  &&  “ (problem_95_pre_z rows ) ” 
  &&  “ (scan_state_z rows k i islower isupper ) ”
  &&  (((row_ptr + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (Znth (k) (rows) ((@nil Z))) 0))
  **  (CharArray.missing_i row_ptr i 0 (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
.

Definition check_dict_case_partial_solve_wit_4 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (islower: Z) (isupper: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH4 : (0 <= i)) (PreH5 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH6 : (0 <= k)) (PreH7 : (k < dict_size_pre)) (PreH8 : (0 < dict_size_pre)) (PreH9 : (dict_size_pre <= 100)) (PreH10 : (rows_well_formed_z rows dict_size_pre )) (PreH11 : (problem_95_pre_z rows )) (PreH12 : (scan_state_z rows k i islower isupper )) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90) ” 
  &&  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65) ” 
  &&  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < (Zlength ((Znth (k) (rows) ((@nil Z)))))) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < dict_size_pre) ” 
  &&  “ (0 < dict_size_pre) ” 
  &&  “ (dict_size_pre <= 100) ” 
  &&  “ (rows_well_formed_z rows dict_size_pre ) ” 
  &&  “ (problem_95_pre_z rows ) ” 
  &&  “ (scan_state_z rows k i islower isupper ) ”
  &&  (((row_ptr + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (Znth (k) (rows) ((@nil Z))) 0))
  **  (CharArray.missing_i row_ptr i 0 (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
.

Definition check_dict_case_partial_solve_wit_5 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (islower: Z) (isupper: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH4 : (0 <= i)) (PreH5 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH6 : (0 <= k)) (PreH7 : (k < dict_size_pre)) (PreH8 : (0 < dict_size_pre)) (PreH9 : (dict_size_pre <= 100)) (PreH10 : (rows_well_formed_z rows dict_size_pre )) (PreH11 : (problem_95_pre_z rows )) (PreH12 : (scan_state_z rows k i islower isupper )) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90) ” 
  &&  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65) ” 
  &&  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < (Zlength ((Znth (k) (rows) ((@nil Z)))))) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < dict_size_pre) ” 
  &&  “ (0 < dict_size_pre) ” 
  &&  “ (dict_size_pre <= 100) ” 
  &&  “ (rows_well_formed_z rows dict_size_pre ) ” 
  &&  “ (problem_95_pre_z rows ) ” 
  &&  “ (scan_state_z rows k i islower isupper ) ”
  &&  (((row_ptr + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (Znth (k) (rows) ((@nil Z))) 0))
  **  (CharArray.missing_i row_ptr i 0 (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
.

Definition check_dict_case_partial_solve_wit_6 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (islower: Z) (isupper: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH5 : (0 <= i)) (PreH6 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH7 : (0 <= k)) (PreH8 : (k < dict_size_pre)) (PreH9 : (0 < dict_size_pre)) (PreH10 : (dict_size_pre <= 100)) (PreH11 : (rows_well_formed_z rows dict_size_pre )) (PreH12 : (problem_95_pre_z rows )) (PreH13 : (scan_state_z rows k i islower isupper )) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97) ” 
  &&  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90) ” 
  &&  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65) ” 
  &&  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < (Zlength ((Znth (k) (rows) ((@nil Z)))))) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < dict_size_pre) ” 
  &&  “ (0 < dict_size_pre) ” 
  &&  “ (dict_size_pre <= 100) ” 
  &&  “ (rows_well_formed_z rows dict_size_pre ) ” 
  &&  “ (problem_95_pre_z rows ) ” 
  &&  “ (scan_state_z rows k i islower isupper ) ”
  &&  (((row_ptr + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (Znth (k) (rows) ((@nil Z))) 0))
  **  (CharArray.missing_i row_ptr i 0 (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
.

Definition check_dict_case_partial_solve_wit_7 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (islower: Z) (isupper: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH6 : (0 <= i)) (PreH7 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH8 : (0 <= k)) (PreH9 : (k < dict_size_pre)) (PreH10 : (0 < dict_size_pre)) (PreH11 : (dict_size_pre <= 100)) (PreH12 : (rows_well_formed_z rows dict_size_pre )) (PreH13 : (problem_95_pre_z rows )) (PreH14 : (scan_state_z rows k i islower isupper )) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122) ” 
  &&  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97) ” 
  &&  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90) ” 
  &&  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65) ” 
  &&  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < (Zlength ((Znth (k) (rows) ((@nil Z)))))) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < dict_size_pre) ” 
  &&  “ (0 < dict_size_pre) ” 
  &&  “ (dict_size_pre <= 100) ” 
  &&  “ (rows_well_formed_z rows dict_size_pre ) ” 
  &&  “ (problem_95_pre_z rows ) ” 
  &&  “ (scan_state_z rows k i islower isupper ) ”
  &&  (((row_ptr + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (Znth (k) (rows) ((@nil Z))) 0))
  **  (CharArray.missing_i row_ptr i 0 (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
.

Definition check_dict_case_partial_solve_wit_8 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (islower: Z) (isupper: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH5 : (0 <= i)) (PreH6 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH7 : (0 <= k)) (PreH8 : (k < dict_size_pre)) (PreH9 : (0 < dict_size_pre)) (PreH10 : (dict_size_pre <= 100)) (PreH11 : (rows_well_formed_z rows dict_size_pre )) (PreH12 : (problem_95_pre_z rows )) (PreH13 : (scan_state_z rows k i islower isupper )) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122) ” 
  &&  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90) ” 
  &&  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65) ” 
  &&  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < (Zlength ((Znth (k) (rows) ((@nil Z)))))) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < dict_size_pre) ” 
  &&  “ (0 < dict_size_pre) ” 
  &&  “ (dict_size_pre <= 100) ” 
  &&  “ (rows_well_formed_z rows dict_size_pre ) ” 
  &&  “ (problem_95_pre_z rows ) ” 
  &&  “ (scan_state_z rows k i islower isupper ) ”
  &&  (((row_ptr + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (Znth (k) (rows) ((@nil Z))) 0))
  **  (CharArray.missing_i row_ptr i 0 (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
.

Definition check_dict_case_partial_solve_wit_9 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (islower: Z) (isupper: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH6 : (0 <= i)) (PreH7 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH8 : (0 <= k)) (PreH9 : (k < dict_size_pre)) (PreH10 : (0 < dict_size_pre)) (PreH11 : (dict_size_pre <= 100)) (PreH12 : (rows_well_formed_z rows dict_size_pre )) (PreH13 : (problem_95_pre_z rows )) (PreH14 : (scan_state_z rows k i islower isupper )) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65) ” 
  &&  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122) ” 
  &&  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90) ” 
  &&  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65) ” 
  &&  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < (Zlength ((Znth (k) (rows) ((@nil Z)))))) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < dict_size_pre) ” 
  &&  “ (0 < dict_size_pre) ” 
  &&  “ (dict_size_pre <= 100) ” 
  &&  “ (rows_well_formed_z rows dict_size_pre ) ” 
  &&  “ (problem_95_pre_z rows ) ” 
  &&  “ (scan_state_z rows k i islower isupper ) ”
  &&  (((row_ptr + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (Znth (k) (rows) ((@nil Z))) 0))
  **  (CharArray.missing_i row_ptr i 0 (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
.

Definition check_dict_case_partial_solve_wit_10 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (islower: Z) (isupper: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH6 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH7 : (0 <= i)) (PreH8 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH9 : (0 <= k)) (PreH10 : (k < dict_size_pre)) (PreH11 : (0 < dict_size_pre)) (PreH12 : (dict_size_pre <= 100)) (PreH13 : (rows_well_formed_z rows dict_size_pre )) (PreH14 : (problem_95_pre_z rows )) (PreH15 : (scan_state_z rows k i islower isupper )) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65) ” 
  &&  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122) ” 
  &&  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97) ” 
  &&  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90) ” 
  &&  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65) ” 
  &&  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < (Zlength ((Znth (k) (rows) ((@nil Z)))))) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < dict_size_pre) ” 
  &&  “ (0 < dict_size_pre) ” 
  &&  “ (dict_size_pre <= 100) ” 
  &&  “ (rows_well_formed_z rows dict_size_pre ) ” 
  &&  “ (problem_95_pre_z rows ) ” 
  &&  “ (scan_state_z rows k i islower isupper ) ”
  &&  (((row_ptr + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (Znth (k) (rows) ((@nil Z))) 0))
  **  (CharArray.missing_i row_ptr i 0 (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
.

Definition check_dict_case_partial_solve_wit_11 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (islower: Z) (isupper: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH6 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH7 : (0 <= i)) (PreH8 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH9 : (0 <= k)) (PreH10 : (k < dict_size_pre)) (PreH11 : (0 < dict_size_pre)) (PreH12 : (dict_size_pre <= 100)) (PreH13 : (rows_well_formed_z rows dict_size_pre )) (PreH14 : (problem_95_pre_z rows )) (PreH15 : (scan_state_z rows k i islower isupper )) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90) ” 
  &&  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65) ” 
  &&  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122) ” 
  &&  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90) ” 
  &&  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65) ” 
  &&  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < (Zlength ((Znth (k) (rows) ((@nil Z)))))) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < dict_size_pre) ” 
  &&  “ (0 < dict_size_pre) ” 
  &&  “ (dict_size_pre <= 100) ” 
  &&  “ (rows_well_formed_z rows dict_size_pre ) ” 
  &&  “ (problem_95_pre_z rows ) ” 
  &&  “ (scan_state_z rows k i islower isupper ) ”
  &&  (((row_ptr + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (Znth (k) (rows) ((@nil Z))) 0))
  **  (CharArray.missing_i row_ptr i 0 (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
.

Definition check_dict_case_partial_solve_wit_12 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (islower: Z) (isupper: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH6 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH7 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH8 : (0 <= i)) (PreH9 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH10 : (0 <= k)) (PreH11 : (k < dict_size_pre)) (PreH12 : (0 < dict_size_pre)) (PreH13 : (dict_size_pre <= 100)) (PreH14 : (rows_well_formed_z rows dict_size_pre )) (PreH15 : (problem_95_pre_z rows )) (PreH16 : (scan_state_z rows k i islower isupper )) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90) ” 
  &&  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65) ” 
  &&  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122) ” 
  &&  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97) ” 
  &&  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90) ” 
  &&  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65) ” 
  &&  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < (Zlength ((Znth (k) (rows) ((@nil Z)))))) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < dict_size_pre) ” 
  &&  “ (0 < dict_size_pre) ” 
  &&  “ (dict_size_pre <= 100) ” 
  &&  “ (rows_well_formed_z rows dict_size_pre ) ” 
  &&  “ (problem_95_pre_z rows ) ” 
  &&  “ (scan_state_z rows k i islower isupper ) ”
  &&  (((row_ptr + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (Znth (k) (rows) ((@nil Z))) 0))
  **  (CharArray.missing_i row_ptr i 0 (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
.

Definition check_dict_case_partial_solve_wit_13 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (islower: Z) (isupper: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH6 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH7 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH8 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH9 : (0 <= i)) (PreH10 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH11 : (0 <= k)) (PreH12 : (k < dict_size_pre)) (PreH13 : (0 < dict_size_pre)) (PreH14 : (dict_size_pre <= 100)) (PreH15 : (rows_well_formed_z rows dict_size_pre )) (PreH16 : (problem_95_pre_z rows )) (PreH17 : (scan_state_z rows k i islower isupper )) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97) ” 
  &&  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90) ” 
  &&  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65) ” 
  &&  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122) ” 
  &&  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97) ” 
  &&  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90) ” 
  &&  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65) ” 
  &&  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < (Zlength ((Znth (k) (rows) ((@nil Z)))))) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < dict_size_pre) ” 
  &&  “ (0 < dict_size_pre) ” 
  &&  “ (dict_size_pre <= 100) ” 
  &&  “ (rows_well_formed_z rows dict_size_pre ) ” 
  &&  “ (problem_95_pre_z rows ) ” 
  &&  “ (scan_state_z rows k i islower isupper ) ”
  &&  (((row_ptr + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (Znth (k) (rows) ((@nil Z))) 0))
  **  (CharArray.missing_i row_ptr i 0 (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
.

Module Type VC_Correct.

Include ptr_array2_Strategy_Correct.
Include char_array_Strategy_Correct.

Axiom proof_of_check_dict_case_safety_wit_1 : check_dict_case_safety_wit_1.
Axiom proof_of_check_dict_case_safety_wit_2 : check_dict_case_safety_wit_2.
Axiom proof_of_check_dict_case_safety_wit_3 : check_dict_case_safety_wit_3.
Axiom proof_of_check_dict_case_safety_wit_4 : check_dict_case_safety_wit_4.
Axiom proof_of_check_dict_case_safety_wit_5 : check_dict_case_safety_wit_5.
Axiom proof_of_check_dict_case_safety_wit_6 : check_dict_case_safety_wit_6.
Axiom proof_of_check_dict_case_safety_wit_7 : check_dict_case_safety_wit_7.
Axiom proof_of_check_dict_case_safety_wit_8 : check_dict_case_safety_wit_8.
Axiom proof_of_check_dict_case_safety_wit_9 : check_dict_case_safety_wit_9.
Axiom proof_of_check_dict_case_safety_wit_10 : check_dict_case_safety_wit_10.
Axiom proof_of_check_dict_case_safety_wit_11 : check_dict_case_safety_wit_11.
Axiom proof_of_check_dict_case_safety_wit_12 : check_dict_case_safety_wit_12.
Axiom proof_of_check_dict_case_safety_wit_13 : check_dict_case_safety_wit_13.
Axiom proof_of_check_dict_case_safety_wit_14 : check_dict_case_safety_wit_14.
Axiom proof_of_check_dict_case_safety_wit_15 : check_dict_case_safety_wit_15.
Axiom proof_of_check_dict_case_safety_wit_16 : check_dict_case_safety_wit_16.
Axiom proof_of_check_dict_case_safety_wit_17 : check_dict_case_safety_wit_17.
Axiom proof_of_check_dict_case_safety_wit_18 : check_dict_case_safety_wit_18.
Axiom proof_of_check_dict_case_safety_wit_19 : check_dict_case_safety_wit_19.
Axiom proof_of_check_dict_case_safety_wit_20 : check_dict_case_safety_wit_20.
Axiom proof_of_check_dict_case_safety_wit_21 : check_dict_case_safety_wit_21.
Axiom proof_of_check_dict_case_safety_wit_22 : check_dict_case_safety_wit_22.
Axiom proof_of_check_dict_case_safety_wit_23 : check_dict_case_safety_wit_23.
Axiom proof_of_check_dict_case_safety_wit_24 : check_dict_case_safety_wit_24.
Axiom proof_of_check_dict_case_safety_wit_25 : check_dict_case_safety_wit_25.
Axiom proof_of_check_dict_case_safety_wit_26 : check_dict_case_safety_wit_26.
Axiom proof_of_check_dict_case_safety_wit_27 : check_dict_case_safety_wit_27.
Axiom proof_of_check_dict_case_safety_wit_28 : check_dict_case_safety_wit_28.
Axiom proof_of_check_dict_case_safety_wit_29 : check_dict_case_safety_wit_29.
Axiom proof_of_check_dict_case_safety_wit_30 : check_dict_case_safety_wit_30.
Axiom proof_of_check_dict_case_safety_wit_31 : check_dict_case_safety_wit_31.
Axiom proof_of_check_dict_case_safety_wit_32 : check_dict_case_safety_wit_32.
Axiom proof_of_check_dict_case_safety_wit_33 : check_dict_case_safety_wit_33.
Axiom proof_of_check_dict_case_safety_wit_34 : check_dict_case_safety_wit_34.
Axiom proof_of_check_dict_case_safety_wit_35 : check_dict_case_safety_wit_35.
Axiom proof_of_check_dict_case_safety_wit_36 : check_dict_case_safety_wit_36.
Axiom proof_of_check_dict_case_safety_wit_37 : check_dict_case_safety_wit_37.
Axiom proof_of_check_dict_case_safety_wit_38 : check_dict_case_safety_wit_38.
Axiom proof_of_check_dict_case_safety_wit_39 : check_dict_case_safety_wit_39.
Axiom proof_of_check_dict_case_safety_wit_40 : check_dict_case_safety_wit_40.
Axiom proof_of_check_dict_case_safety_wit_41 : check_dict_case_safety_wit_41.
Axiom proof_of_check_dict_case_safety_wit_42 : check_dict_case_safety_wit_42.
Axiom proof_of_check_dict_case_entail_wit_1 : check_dict_case_entail_wit_1.
Axiom proof_of_check_dict_case_entail_wit_2 : check_dict_case_entail_wit_2.
Axiom proof_of_check_dict_case_entail_wit_3 : check_dict_case_entail_wit_3.
Axiom proof_of_check_dict_case_entail_wit_4 : check_dict_case_entail_wit_4.
Axiom proof_of_check_dict_case_entail_wit_5 : check_dict_case_entail_wit_5.
Axiom proof_of_check_dict_case_entail_wit_6_1 : check_dict_case_entail_wit_6_1.
Axiom proof_of_check_dict_case_entail_wit_6_2 : check_dict_case_entail_wit_6_2.
Axiom proof_of_check_dict_case_entail_wit_7 : check_dict_case_entail_wit_7.
Axiom proof_of_check_dict_case_entail_wit_8 : check_dict_case_entail_wit_8.
Axiom proof_of_check_dict_case_return_wit_1 : check_dict_case_return_wit_1.
Axiom proof_of_check_dict_case_return_wit_2 : check_dict_case_return_wit_2.
Axiom proof_of_check_dict_case_return_wit_3 : check_dict_case_return_wit_3.
Axiom proof_of_check_dict_case_return_wit_4 : check_dict_case_return_wit_4.
Axiom proof_of_check_dict_case_return_wit_5 : check_dict_case_return_wit_5.
Axiom proof_of_check_dict_case_return_wit_6 : check_dict_case_return_wit_6.
Axiom proof_of_check_dict_case_return_wit_7 : check_dict_case_return_wit_7.
Axiom proof_of_check_dict_case_partial_solve_wit_1 : check_dict_case_partial_solve_wit_1.
Axiom proof_of_check_dict_case_partial_solve_wit_2 : check_dict_case_partial_solve_wit_2.
Axiom proof_of_check_dict_case_partial_solve_wit_3 : check_dict_case_partial_solve_wit_3.
Axiom proof_of_check_dict_case_partial_solve_wit_4 : check_dict_case_partial_solve_wit_4.
Axiom proof_of_check_dict_case_partial_solve_wit_5 : check_dict_case_partial_solve_wit_5.
Axiom proof_of_check_dict_case_partial_solve_wit_6 : check_dict_case_partial_solve_wit_6.
Axiom proof_of_check_dict_case_partial_solve_wit_7 : check_dict_case_partial_solve_wit_7.
Axiom proof_of_check_dict_case_partial_solve_wit_8 : check_dict_case_partial_solve_wit_8.
Axiom proof_of_check_dict_case_partial_solve_wit_9 : check_dict_case_partial_solve_wit_9.
Axiom proof_of_check_dict_case_partial_solve_wit_10 : check_dict_case_partial_solve_wit_10.
Axiom proof_of_check_dict_case_partial_solve_wit_11 : check_dict_case_partial_solve_wit_11.
Axiom proof_of_check_dict_case_partial_solve_wit_12 : check_dict_case_partial_solve_wit_12.
Axiom proof_of_check_dict_case_partial_solve_wit_13 : check_dict_case_partial_solve_wit_13.

End VC_Correct.
