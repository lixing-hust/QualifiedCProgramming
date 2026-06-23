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
Require Import coins_158.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import ptr_array2_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import ptr_array2_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_proof.
From SimpleC.StdLib Require Import string_strategy_goal.
From SimpleC.StdLib Require Import string_strategy_proof.

(*----- Function find_max -----*)

Definition find_max_safety_wit_1 := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (PreH1 : (0 < words_size_pre)) (PreH2 : (words_size_pre <= 100)) (PreH3 : (rows_well_formed_158 rows words_size_pre )) (PreH4 : (problem_158_pre_z rows )) ,
  ((( &( "ch" ) )) # Int  |->_)
  **  ((( &( "len" ) )) # Int  |->_)
  **  ((( &( "k" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "best_idx" ) )) # Int  |->_)
  **  ((( &( "cmp" ) )) # Int  |->_)
  **  ((( &( "unique" ) )) # Int  |->_)
  **  ((( &( "maxu" ) )) # Int  |->_)
  **  (IntArray.undef_full ( &( "seen" ) ) 128 )
  **  ((( &( "cur" ) )) # Ptr  |->_)
  **  ((( &( "max" ) )) # Ptr  |->_)
  **  ((( &( "words_size" ) )) # Int  |-> words_size_pre)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  (CharPtrArray2.full words_pre words_size_pre rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition find_max_safety_wit_2 := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z)  __default__List_Z (PreH1 : (0 <= (Zlength ((Znth 0 rows __default__List_Z))))) (PreH2 : (0 < words_size_pre)) (PreH3 : (words_size_pre <= 100)) (PreH4 : (rows_well_formed_158 rows words_size_pre )) (PreH5 : (problem_158_pre_z rows )) ,
  (CharPtrArray2.full words_pre words_size_pre rows )
  **  ((( &( "ch" ) )) # Int  |->_)
  **  ((( &( "len" ) )) # Int  |->_)
  **  ((( &( "k" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "best_idx" ) )) # Int  |->_)
  **  ((( &( "cmp" ) )) # Int  |->_)
  **  ((( &( "unique" ) )) # Int  |->_)
  **  ((( &( "maxu" ) )) # Int  |->_)
  **  (IntArray.undef_full ( &( "seen" ) ) 128 )
  **  ((( &( "cur" ) )) # Ptr  |->_)
  **  ((( &( "max" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "words_size" ) )) # Int  |-> words_size_pre)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition find_max_safety_wit_3 := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z)  __default__List_Z (PreH1 : (0 <= (Zlength ((Znth 0 rows __default__List_Z))))) (PreH2 : (0 < words_size_pre)) (PreH3 : (words_size_pre <= 100)) (PreH4 : (rows_well_formed_158 rows words_size_pre )) (PreH5 : (problem_158_pre_z rows )) ,
  (CharPtrArray2.full words_pre words_size_pre rows )
  **  ((( &( "ch" ) )) # Int  |->_)
  **  ((( &( "len" ) )) # Int  |->_)
  **  ((( &( "k" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "best_idx" ) )) # Int  |->_)
  **  ((( &( "cmp" ) )) # Int  |->_)
  **  ((( &( "unique" ) )) # Int  |->_)
  **  ((( &( "maxu" ) )) # Int  |-> 0)
  **  (IntArray.undef_full ( &( "seen" ) ) 128 )
  **  ((( &( "cur" ) )) # Ptr  |->_)
  **  ((( &( "max" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "words_size" ) )) # Int  |-> words_size_pre)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition find_max_safety_wit_4 := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z)  __default__List_Z (PreH1 : (0 <= (Zlength ((Znth 0 rows __default__List_Z))))) (PreH2 : (0 < words_size_pre)) (PreH3 : (words_size_pre <= 100)) (PreH4 : (rows_well_formed_158 rows words_size_pre )) (PreH5 : (problem_158_pre_z rows )) ,
  (CharPtrArray2.full words_pre words_size_pre rows )
  **  ((( &( "ch" ) )) # Int  |->_)
  **  ((( &( "len" ) )) # Int  |->_)
  **  ((( &( "k" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "best_idx" ) )) # Int  |->_)
  **  ((( &( "cmp" ) )) # Int  |->_)
  **  ((( &( "unique" ) )) # Int  |-> 0)
  **  ((( &( "maxu" ) )) # Int  |-> 0)
  **  (IntArray.undef_full ( &( "seen" ) ) 128 )
  **  ((( &( "cur" ) )) # Ptr  |->_)
  **  ((( &( "max" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "words_size" ) )) # Int  |-> words_size_pre)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition find_max_safety_wit_5 := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z)  __default__List_Z (PreH1 : (0 <= (Zlength ((Znth 0 rows __default__List_Z))))) (PreH2 : (0 < words_size_pre)) (PreH3 : (words_size_pre <= 100)) (PreH4 : (rows_well_formed_158 rows words_size_pre )) (PreH5 : (problem_158_pre_z rows )) ,
  (CharPtrArray2.full words_pre words_size_pre rows )
  **  ((( &( "ch" ) )) # Int  |->_)
  **  ((( &( "len" ) )) # Int  |->_)
  **  ((( &( "k" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "best_idx" ) )) # Int  |->_)
  **  ((( &( "cmp" ) )) # Int  |-> 0)
  **  ((( &( "unique" ) )) # Int  |-> 0)
  **  ((( &( "maxu" ) )) # Int  |-> 0)
  **  (IntArray.undef_full ( &( "seen" ) ) 128 )
  **  ((( &( "cur" ) )) # Ptr  |->_)
  **  ((( &( "max" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "words_size" ) )) # Int  |-> words_size_pre)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition find_max_safety_wit_6 := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z)  __default__List_Z (PreH1 : (0 <= (Zlength ((Znth 0 rows __default__List_Z))))) (PreH2 : (0 < words_size_pre)) (PreH3 : (words_size_pre <= 100)) (PreH4 : (rows_well_formed_158 rows words_size_pre )) (PreH5 : (problem_158_pre_z rows )) ,
  (CharPtrArray2.full words_pre words_size_pre rows )
  **  ((( &( "ch" ) )) # Int  |->_)
  **  ((( &( "len" ) )) # Int  |->_)
  **  ((( &( "k" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "best_idx" ) )) # Int  |-> 0)
  **  ((( &( "cmp" ) )) # Int  |-> 0)
  **  ((( &( "unique" ) )) # Int  |-> 0)
  **  ((( &( "maxu" ) )) # Int  |-> 0)
  **  (IntArray.undef_full ( &( "seen" ) ) 128 )
  **  ((( &( "cur" ) )) # Ptr  |->_)
  **  ((( &( "max" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "words_size" ) )) # Int  |-> words_size_pre)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition find_max_safety_wit_7 := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z)  __default__List_Z (PreH1 : (0 <= (Zlength ((Znth 0 rows __default__List_Z))))) (PreH2 : (0 < words_size_pre)) (PreH3 : (words_size_pre <= 100)) (PreH4 : (rows_well_formed_158 rows words_size_pre )) (PreH5 : (problem_158_pre_z rows )) ,
  (CharPtrArray2.full words_pre words_size_pre rows )
  **  ((( &( "ch" ) )) # Int  |->_)
  **  ((( &( "len" ) )) # Int  |->_)
  **  ((( &( "k" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "best_idx" ) )) # Int  |-> 0)
  **  ((( &( "cmp" ) )) # Int  |-> 0)
  **  ((( &( "unique" ) )) # Int  |-> 0)
  **  ((( &( "maxu" ) )) # Int  |-> 0)
  **  (IntArray.undef_full ( &( "seen" ) ) 128 )
  **  ((( &( "cur" ) )) # Ptr  |-> 0)
  **  ((( &( "max" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "words_size" ) )) # Int  |-> words_size_pre)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition find_max_safety_wit_8 := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z)  __default__List_Z (PreH1 : (0 <= (Zlength ((Znth 0 rows __default__List_Z))))) (PreH2 : (0 < words_size_pre)) (PreH3 : (words_size_pre <= 100)) (PreH4 : (rows_well_formed_158 rows words_size_pre )) (PreH5 : (problem_158_pre_z rows )) ,
  (CharPtrArray2.full words_pre words_size_pre rows )
  **  ((( &( "ch" ) )) # Int  |->_)
  **  ((( &( "len" ) )) # Int  |->_)
  **  ((( &( "k" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "best_idx" ) )) # Int  |-> 0)
  **  ((( &( "cmp" ) )) # Int  |-> 0)
  **  ((( &( "unique" ) )) # Int  |-> 0)
  **  ((( &( "maxu" ) )) # Int  |-> 0)
  **  (IntArray.undef_full ( &( "seen" ) ) 128 )
  **  ((( &( "cur" ) )) # Ptr  |-> 0)
  **  ((( &( "max" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "words_size" ) )) # Int  |-> words_size_pre)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition find_max_safety_wit_9 := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z)  __default__List_Z (PreH1 : (0 <= (Zlength ((Znth 0 rows __default__List_Z))))) (PreH2 : (0 < words_size_pre)) (PreH3 : (words_size_pre <= 100)) (PreH4 : (rows_well_formed_158 rows words_size_pre )) (PreH5 : (problem_158_pre_z rows )) ,
  (CharPtrArray2.full words_pre words_size_pre rows )
  **  ((( &( "ch" ) )) # Int  |->_)
  **  ((( &( "len" ) )) # Int  |->_)
  **  ((( &( "k" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "best_idx" ) )) # Int  |-> 0)
  **  ((( &( "cmp" ) )) # Int  |-> 0)
  **  ((( &( "unique" ) )) # Int  |-> 0)
  **  ((( &( "maxu" ) )) # Int  |-> 0)
  **  (IntArray.undef_full ( &( "seen" ) ) 128 )
  **  ((( &( "cur" ) )) # Ptr  |-> 0)
  **  ((( &( "max" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "words_size" ) )) # Int  |-> words_size_pre)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition find_max_safety_wit_10 := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z)  __default__List_Z (PreH1 : (0 <= (Zlength ((Znth 0 rows __default__List_Z))))) (PreH2 : (0 < words_size_pre)) (PreH3 : (words_size_pre <= 100)) (PreH4 : (rows_well_formed_158 rows words_size_pre )) (PreH5 : (problem_158_pre_z rows )) ,
  (CharPtrArray2.full words_pre words_size_pre rows )
  **  ((( &( "ch" ) )) # Int  |->_)
  **  ((( &( "len" ) )) # Int  |-> 0)
  **  ((( &( "k" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "best_idx" ) )) # Int  |-> 0)
  **  ((( &( "cmp" ) )) # Int  |-> 0)
  **  ((( &( "unique" ) )) # Int  |-> 0)
  **  ((( &( "maxu" ) )) # Int  |-> 0)
  **  (IntArray.undef_full ( &( "seen" ) ) 128 )
  **  ((( &( "cur" ) )) # Ptr  |-> 0)
  **  ((( &( "max" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "words_size" ) )) # Int  |-> words_size_pre)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition find_max_safety_wit_11 := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z)  __default__List_Z (PreH1 : (0 <= (Zlength ((Znth 0 rows __default__List_Z))))) (PreH2 : (0 < words_size_pre)) (PreH3 : (words_size_pre <= 100)) (PreH4 : (rows_well_formed_158 rows words_size_pre )) (PreH5 : (problem_158_pre_z rows )) ,
  (CharPtrArray2.full words_pre words_size_pre rows )
  **  ((( &( "ch" ) )) # Int  |-> 0)
  **  ((( &( "len" ) )) # Int  |-> 0)
  **  ((( &( "k" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "best_idx" ) )) # Int  |-> 0)
  **  ((( &( "cmp" ) )) # Int  |-> 0)
  **  ((( &( "unique" ) )) # Int  |-> 0)
  **  ((( &( "maxu" ) )) # Int  |-> 0)
  **  (IntArray.undef_full ( &( "seen" ) ) 128 )
  **  ((( &( "cur" ) )) # Ptr  |-> 0)
  **  ((( &( "max" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "words_size" ) )) # Int  |-> words_size_pre)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition find_max_safety_wit_12 := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (best_idx: Z) (unique: Z) (maxu: Z) (cmp: Z) (ch: Z) (len: Z) (j: Z) (i: Z) (cur: Z) (max: Z) (k: Z) (PreH1 : (0 <= k)) (PreH2 : (k <= 128)) (PreH3 : (j = 0)) (PreH4 : (len = 0)) (PreH5 : (ch = 0)) (PreH6 : (maxu = 0)) (PreH7 : (unique = 0)) (PreH8 : (best_idx = 0)) (PreH9 : (0 < words_size_pre)) (PreH10 : (words_size_pre <= 100)) (PreH11 : (rows_well_formed_158 rows words_size_pre )) (PreH12 : (problem_158_pre_z rows )) ,
  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "words_size" ) )) # Int  |-> words_size_pre)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "max" ) )) # Ptr  |-> max)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "maxu" ) )) # Int  |-> maxu)
  **  ((( &( "unique" ) )) # Int  |-> unique)
  **  ((( &( "best_idx" ) )) # Int  |-> best_idx)
  **  (CharPtrArray2.full words_pre words_size_pre rows )
  **  (IntArray.seg ( &( "seen" ) ) 0 k (zeros (k)) )
  **  (IntArray.undef_seg ( &( "seen" ) ) k 128 )
|--
  “ (128 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 128) ”
.

Definition find_max_safety_wit_13 := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (best_idx: Z) (unique: Z) (maxu: Z) (cmp: Z) (ch: Z) (len: Z) (j: Z) (i: Z) (cur: Z) (max: Z) (k: Z) (PreH1 : (k < 128)) (PreH2 : (0 <= k)) (PreH3 : (k <= 128)) (PreH4 : (j = 0)) (PreH5 : (len = 0)) (PreH6 : (ch = 0)) (PreH7 : (maxu = 0)) (PreH8 : (unique = 0)) (PreH9 : (best_idx = 0)) (PreH10 : (0 < words_size_pre)) (PreH11 : (words_size_pre <= 100)) (PreH12 : (rows_well_formed_158 rows words_size_pre )) (PreH13 : (problem_158_pre_z rows )) ,
  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "words_size" ) )) # Int  |-> words_size_pre)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "max" ) )) # Ptr  |-> max)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "maxu" ) )) # Int  |-> maxu)
  **  ((( &( "unique" ) )) # Int  |-> unique)
  **  ((( &( "best_idx" ) )) # Int  |-> best_idx)
  **  (CharPtrArray2.full words_pre words_size_pre rows )
  **  (IntArray.seg ( &( "seen" ) ) 0 k (zeros (k)) )
  **  (IntArray.undef_seg ( &( "seen" ) ) k 128 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition find_max_safety_wit_14 := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (best_idx: Z) (unique: Z) (maxu: Z) (cmp: Z) (ch: Z) (len: Z) (j: Z) (i: Z) (cur: Z) (max: Z) (k: Z) (PreH1 : (k < 128)) (PreH2 : (0 <= k)) (PreH3 : (k <= 128)) (PreH4 : (j = 0)) (PreH5 : (len = 0)) (PreH6 : (ch = 0)) (PreH7 : (maxu = 0)) (PreH8 : (unique = 0)) (PreH9 : (best_idx = 0)) (PreH10 : (0 < words_size_pre)) (PreH11 : (words_size_pre <= 100)) (PreH12 : (rows_well_formed_158 rows words_size_pre )) (PreH13 : (problem_158_pre_z rows )) ,
  (IntArray.seg ( &( "seen" ) ) 0 (k + 1 ) (app ((zeros (k))) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "seen" ) ) (k + 1 ) 128 )
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "words_size" ) )) # Int  |-> words_size_pre)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "max" ) )) # Ptr  |-> max)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "maxu" ) )) # Int  |-> maxu)
  **  ((( &( "unique" ) )) # Int  |-> unique)
  **  ((( &( "best_idx" ) )) # Int  |-> best_idx)
  **  (CharPtrArray2.full words_pre words_size_pre rows )
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition find_max_safety_wit_15 := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (best_idx: Z) (unique: Z) (maxu: Z) (cmp: Z) (ch: Z) (len: Z) (j: Z) (i: Z) (cur: Z) (max: Z) (k: Z) (PreH1 : (k < 128)) (PreH2 : (0 <= k)) (PreH3 : (k <= 128)) (PreH4 : (j = 0)) (PreH5 : (len = 0)) (PreH6 : (ch = 0)) (PreH7 : (maxu = 0)) (PreH8 : (unique = 0)) (PreH9 : (best_idx = 0)) (PreH10 : (0 < words_size_pre)) (PreH11 : (words_size_pre <= 100)) (PreH12 : (rows_well_formed_158 rows words_size_pre )) (PreH13 : (problem_158_pre_z rows )) ,
  (IntArray.seg ( &( "seen" ) ) 0 (k + 1 ) (app ((zeros (k))) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "seen" ) ) (k + 1 ) 128 )
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "words_size" ) )) # Int  |-> words_size_pre)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "max" ) )) # Ptr  |-> max)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "maxu" ) )) # Int  |-> maxu)
  **  ((( &( "unique" ) )) # Int  |-> unique)
  **  ((( &( "best_idx" ) )) # Int  |-> best_idx)
  **  (CharPtrArray2.full words_pre words_size_pre rows )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition find_max_safety_wit_16 := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (best_idx: Z) (unique: Z) (maxu: Z) (cmp: Z) (ch: Z) (len: Z) (j: Z) (i: Z) (cur: Z) (max: Z) (k: Z) (PreH1 : (k >= 128)) (PreH2 : (0 <= k)) (PreH3 : (k <= 128)) (PreH4 : (j = 0)) (PreH5 : (len = 0)) (PreH6 : (ch = 0)) (PreH7 : (maxu = 0)) (PreH8 : (unique = 0)) (PreH9 : (best_idx = 0)) (PreH10 : (0 < words_size_pre)) (PreH11 : (words_size_pre <= 100)) (PreH12 : (rows_well_formed_158 rows words_size_pre )) (PreH13 : (problem_158_pre_z rows )) ,
  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "words_size" ) )) # Int  |-> words_size_pre)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "max" ) )) # Ptr  |-> max)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "maxu" ) )) # Int  |-> maxu)
  **  ((( &( "unique" ) )) # Int  |-> unique)
  **  ((( &( "best_idx" ) )) # Int  |-> best_idx)
  **  (CharPtrArray2.full words_pre words_size_pre rows )
  **  (IntArray.seg ( &( "seen" ) ) 0 k (zeros (k)) )
  **  (IntArray.undef_seg ( &( "seen" ) ) k 128 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition find_max_safety_wit_17 := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (seen_l: (@list Z)) (i: Z) (max: Z) (cur: Z) (k: Z) (j: Z) (cmp: Z) (len: Z) (ch: Z) (best_idx: Z) (maxu: Z) (unique: Z) (PreH1 : (0 <= i)) (PreH2 : (i < words_size_pre)) (PreH3 : (0 < words_size_pre)) (PreH4 : (words_size_pre <= 100)) (PreH5 : (0 <= best_idx)) (PreH6 : (best_idx < words_size_pre)) (PreH7 : (0 <= maxu)) (PreH8 : (maxu <= 128)) (PreH9 : (0 <= unique)) (PreH10 : (unique <= 128)) (PreH11 : (rows_well_formed_158 rows words_size_pre )) (PreH12 : (problem_158_pre_z rows )) (PreH13 : (best_prefix_state_158 rows i best_idx maxu )) (PreH14 : ((Zlength (seen_l)) = 128)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "words_size" ) )) # Int  |-> words_size_pre)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "max" ) )) # Ptr  |-> max)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "best_idx" ) )) # Int  |-> best_idx)
  **  ((( &( "maxu" ) )) # Int  |-> maxu)
  **  ((( &( "unique" ) )) # Int  |-> unique)
  **  (CharPtrArray2.missing_i words_pre words_size_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
  **  (IntArray.full ( &( "seen" ) ) 128 seen_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition find_max_safety_wit_18 := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (seen_l: (@list Z)) (unique: Z) (maxu: Z) (best_idx: Z) (ch: Z) (len: Z) (cmp: Z) (j: Z) (cur: Z) (max: Z) (i: Z) (k: Z) (PreH1 : (0 <= k)) (PreH2 : (k <= 128)) (PreH3 : (0 <= i)) (PreH4 : (i < words_size_pre)) (PreH5 : (0 < words_size_pre)) (PreH6 : (words_size_pre <= 100)) (PreH7 : (0 <= best_idx)) (PreH8 : (best_idx < words_size_pre)) (PreH9 : (0 <= maxu)) (PreH10 : (maxu <= 128)) (PreH11 : (0 <= unique)) (PreH12 : (unique <= 128)) (PreH13 : (rows_well_formed_158 rows words_size_pre )) (PreH14 : (problem_158_pre_z rows )) (PreH15 : (best_prefix_state_158 rows i best_idx maxu )) (PreH16 : ((Zlength (seen_l)) = 128)) (PreH17 : (reset_prefix_state_158 k seen_l )) ,
  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "words_size" ) )) # Int  |-> words_size_pre)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "max" ) )) # Ptr  |-> max)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "best_idx" ) )) # Int  |-> best_idx)
  **  ((( &( "maxu" ) )) # Int  |-> maxu)
  **  ((( &( "unique" ) )) # Int  |-> unique)
  **  (CharPtrArray2.missing_i words_pre words_size_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
  **  (IntArray.full ( &( "seen" ) ) 128 seen_l )
|--
  “ (128 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 128) ”
.

Definition find_max_safety_wit_19 := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (seen_l: (@list Z)) (unique: Z) (maxu: Z) (best_idx: Z) (ch: Z) (len: Z) (cmp: Z) (j: Z) (cur: Z) (max: Z) (i: Z) (k: Z) (PreH1 : (k < 128)) (PreH2 : (0 <= k)) (PreH3 : (k <= 128)) (PreH4 : (0 <= i)) (PreH5 : (i < words_size_pre)) (PreH6 : (0 < words_size_pre)) (PreH7 : (words_size_pre <= 100)) (PreH8 : (0 <= best_idx)) (PreH9 : (best_idx < words_size_pre)) (PreH10 : (0 <= maxu)) (PreH11 : (maxu <= 128)) (PreH12 : (0 <= unique)) (PreH13 : (unique <= 128)) (PreH14 : (rows_well_formed_158 rows words_size_pre )) (PreH15 : (problem_158_pre_z rows )) (PreH16 : (best_prefix_state_158 rows i best_idx maxu )) (PreH17 : ((Zlength (seen_l)) = 128)) (PreH18 : (reset_prefix_state_158 k seen_l )) ,
  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "words_size" ) )) # Int  |-> words_size_pre)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "max" ) )) # Ptr  |-> max)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "best_idx" ) )) # Int  |-> best_idx)
  **  ((( &( "maxu" ) )) # Int  |-> maxu)
  **  ((( &( "unique" ) )) # Int  |-> unique)
  **  (CharPtrArray2.missing_i words_pre words_size_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
  **  (IntArray.full ( &( "seen" ) ) 128 seen_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition find_max_safety_wit_20 := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (seen_l: (@list Z)) (unique: Z) (maxu: Z) (best_idx: Z) (ch: Z) (len: Z) (cmp: Z) (j: Z) (cur: Z) (max: Z) (i: Z) (k: Z) (PreH1 : (0 <= (Zlength ((Znth (i) (rows) ((@nil Z))))))) (PreH2 : (k < 128)) (PreH3 : (0 <= k)) (PreH4 : (k <= 128)) (PreH5 : (0 <= i)) (PreH6 : (i < words_size_pre)) (PreH7 : (0 < words_size_pre)) (PreH8 : (words_size_pre <= 100)) (PreH9 : (0 <= best_idx)) (PreH10 : (best_idx < words_size_pre)) (PreH11 : (0 <= maxu)) (PreH12 : (maxu <= 128)) (PreH13 : (0 <= unique)) (PreH14 : (unique <= 128)) (PreH15 : (rows_well_formed_158 rows words_size_pre )) (PreH16 : (problem_158_pre_z rows )) (PreH17 : (best_prefix_state_158 rows i best_idx maxu )) (PreH18 : ((Zlength (seen_l)) = 128)) (PreH19 : (reset_prefix_state_158 k seen_l )) ,
  (IntArray.full ( &( "seen" ) ) 128 (replace_Znth (k) (0) (seen_l)) )
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "words_size" ) )) # Int  |-> words_size_pre)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "max" ) )) # Ptr  |-> max)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "best_idx" ) )) # Int  |-> best_idx)
  **  ((( &( "maxu" ) )) # Int  |-> maxu)
  **  ((( &( "unique" ) )) # Int  |-> unique)
  **  (CharPtrArray2.missing_i words_pre words_size_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition find_max_safety_wit_21 := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (seen_l: (@list Z)) (unique: Z) (maxu: Z) (best_idx: Z) (ch: Z) (len: Z) (cmp: Z) (j: Z) (cur: Z) (max: Z) (i: Z) (k: Z) (PreH1 : (0 <= (Zlength ((Znth (i) (rows) ((@nil Z))))))) (PreH2 : (k < 128)) (PreH3 : (0 <= k)) (PreH4 : (k <= 128)) (PreH5 : (0 <= i)) (PreH6 : (i < words_size_pre)) (PreH7 : (0 < words_size_pre)) (PreH8 : (words_size_pre <= 100)) (PreH9 : (0 <= best_idx)) (PreH10 : (best_idx < words_size_pre)) (PreH11 : (0 <= maxu)) (PreH12 : (maxu <= 128)) (PreH13 : (0 <= unique)) (PreH14 : (unique <= 128)) (PreH15 : (rows_well_formed_158 rows words_size_pre )) (PreH16 : (problem_158_pre_z rows )) (PreH17 : (best_prefix_state_158 rows i best_idx maxu )) (PreH18 : ((Zlength (seen_l)) = 128)) (PreH19 : (reset_prefix_state_158 k seen_l )) ,
  (IntArray.full ( &( "seen" ) ) 128 (replace_Znth (k) (0) (seen_l)) )
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "words_size" ) )) # Int  |-> words_size_pre)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "max" ) )) # Ptr  |-> max)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "best_idx" ) )) # Int  |-> best_idx)
  **  ((( &( "maxu" ) )) # Int  |-> maxu)
  **  ((( &( "unique" ) )) # Int  |-> unique)
  **  (CharPtrArray2.missing_i words_pre words_size_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition find_max_safety_wit_22 := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (i: Z) (max: Z) (k: Z) (j: Z) (cmp: Z) (ch: Z) (best_idx: Z) (maxu: Z) (unique: Z) (retval: Z) (PreH1 : (retval = (string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))))) (PreH2 : (0 <= ((string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < words_size_pre)) (PreH5 : (0 < words_size_pre)) (PreH6 : (words_size_pre <= 100)) (PreH7 : (0 <= best_idx)) (PreH8 : (best_idx < words_size_pre)) (PreH9 : (0 <= maxu)) (PreH10 : (maxu <= 128)) (PreH11 : (0 <= unique)) (PreH12 : (unique <= 128)) (PreH13 : (rows_well_formed_158 rows words_size_pre )) (PreH14 : (problem_158_pre_z rows )) (PreH15 : (best_prefix_state_158 rows i best_idx maxu )) (PreH16 : (valid_string (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) )) (PreH17 : ((string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX)) (PreH18 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = ((string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) ,
  (store_string row_ptr (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "words_size" ) )) # Int  |-> words_size_pre)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "max" ) )) # Ptr  |-> max)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "len" ) )) # Int  |-> retval)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "best_idx" ) )) # Int  |-> best_idx)
  **  ((( &( "maxu" ) )) # Int  |-> maxu)
  **  ((( &( "unique" ) )) # Int  |-> unique)
  **  (CharPtrArray2.missing_i words_pre words_size_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full ( &( "seen" ) ) 128 (zeros (128)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition find_max_safety_wit_23 := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (i: Z) (max: Z) (k: Z) (j: Z) (cmp: Z) (ch: Z) (best_idx: Z) (maxu: Z) (unique: Z) (retval: Z) (PreH1 : (retval = (string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))))) (PreH2 : (0 <= ((string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < words_size_pre)) (PreH5 : (0 < words_size_pre)) (PreH6 : (words_size_pre <= 100)) (PreH7 : (0 <= best_idx)) (PreH8 : (best_idx < words_size_pre)) (PreH9 : (0 <= maxu)) (PreH10 : (maxu <= 128)) (PreH11 : (0 <= unique)) (PreH12 : (unique <= 128)) (PreH13 : (rows_well_formed_158 rows words_size_pre )) (PreH14 : (problem_158_pre_z rows )) (PreH15 : (best_prefix_state_158 rows i best_idx maxu )) (PreH16 : (valid_string (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) )) (PreH17 : ((string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX)) (PreH18 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = ((string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) ,
  (store_string row_ptr (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "words_size" ) )) # Int  |-> words_size_pre)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "max" ) )) # Ptr  |-> max)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "len" ) )) # Int  |-> retval)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "best_idx" ) )) # Int  |-> best_idx)
  **  ((( &( "maxu" ) )) # Int  |-> maxu)
  **  ((( &( "unique" ) )) # Int  |-> 0)
  **  (CharPtrArray2.missing_i words_pre words_size_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full ( &( "seen" ) ) 128 (zeros (128)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition find_max_safety_wit_24 := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (i: Z) (max: Z) (k: Z) (cmp: Z) (ch: Z) (best_idx: Z) (maxu: Z) (unique: Z) (retval: Z) (PreH1 : (retval = (string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))))) (PreH2 : (0 <= ((string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < words_size_pre)) (PreH5 : (0 < words_size_pre)) (PreH6 : (words_size_pre <= 100)) (PreH7 : (0 <= best_idx)) (PreH8 : (best_idx < words_size_pre)) (PreH9 : (0 <= maxu)) (PreH10 : (maxu <= 128)) (PreH11 : (0 <= unique)) (PreH12 : (unique <= 128)) (PreH13 : (rows_well_formed_158 rows words_size_pre )) (PreH14 : (problem_158_pre_z rows )) (PreH15 : (best_prefix_state_158 rows i best_idx maxu )) (PreH16 : (valid_string (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) )) (PreH17 : ((string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX)) (PreH18 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = ((string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) ,
  (store_string row_ptr (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "words_size" ) )) # Int  |-> words_size_pre)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "max" ) )) # Ptr  |-> max)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "j" ) )) # Int  |-> 0)
  **  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "len" ) )) # Int  |-> retval)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "best_idx" ) )) # Int  |-> best_idx)
  **  ((( &( "maxu" ) )) # Int  |-> maxu)
  **  ((( &( "unique" ) )) # Int  |-> 0)
  **  (CharPtrArray2.missing_i words_pre words_size_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full ( &( "seen" ) ) 128 (zeros (128)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition find_max_safety_wit_25 := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (seen_l: (@list Z)) (j: Z) (len: Z) (i: Z) (max: Z) (k: Z) (cmp: Z) (ch: Z) (best_idx: Z) (maxu: Z) (unique: Z) (PreH1 : (0 <= (Zlength ((Znth (i) (rows) ((@nil Z))))))) (PreH2 : (0 <= j)) (PreH3 : (j < len)) (PreH4 : (0 <= i)) (PreH5 : (i < words_size_pre)) (PreH6 : (0 < words_size_pre)) (PreH7 : (words_size_pre <= 100)) (PreH8 : (0 <= ch)) (PreH9 : (ch < 128)) (PreH10 : (ch = (Znth (j) ((Znth (i) (rows) ((@nil Z)))) (0)))) (PreH11 : (0 <= best_idx)) (PreH12 : (best_idx < words_size_pre)) (PreH13 : (0 <= maxu)) (PreH14 : (maxu <= 128)) (PreH15 : (0 <= unique)) (PreH16 : (unique <= 128)) (PreH17 : (len = (string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))))) (PreH18 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = (len + 1 ))) (PreH19 : (valid_string (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) )) (PreH20 : ((Zlength (seen_l)) = 128)) (PreH21 : (rows_well_formed_158 rows words_size_pre )) (PreH22 : (problem_158_pre_z rows )) (PreH23 : (best_prefix_state_158 rows i best_idx maxu )) (PreH24 : (count_scan_state_158 (Znth (i) (rows) ((@nil Z))) j seen_l unique )) ,
  (IntArray.full ( &( "seen" ) ) 128 seen_l )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "words_size" ) )) # Int  |-> words_size_pre)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "max" ) )) # Ptr  |-> max)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "best_idx" ) )) # Int  |-> best_idx)
  **  ((( &( "maxu" ) )) # Int  |-> maxu)
  **  ((( &( "unique" ) )) # Int  |-> unique)
  **  (CharPtrArray2.missing_i words_pre words_size_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition find_max_safety_wit_26 := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (seen_l: (@list Z)) (j: Z) (len: Z) (i: Z) (max: Z) (k: Z) (cmp: Z) (ch: Z) (best_idx: Z) (maxu: Z) (unique: Z) (PreH1 : ((Znth ch seen_l 0) = 0)) (PreH2 : (0 <= (Zlength ((Znth (i) (rows) ((@nil Z))))))) (PreH3 : (0 <= j)) (PreH4 : (j < len)) (PreH5 : (0 <= i)) (PreH6 : (i < words_size_pre)) (PreH7 : (0 < words_size_pre)) (PreH8 : (words_size_pre <= 100)) (PreH9 : (0 <= ch)) (PreH10 : (ch < 128)) (PreH11 : (ch = (Znth (j) ((Znth (i) (rows) ((@nil Z)))) (0)))) (PreH12 : (0 <= best_idx)) (PreH13 : (best_idx < words_size_pre)) (PreH14 : (0 <= maxu)) (PreH15 : (maxu <= 128)) (PreH16 : (0 <= unique)) (PreH17 : (unique <= 128)) (PreH18 : (len = (string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))))) (PreH19 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = (len + 1 ))) (PreH20 : (valid_string (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) )) (PreH21 : ((Zlength (seen_l)) = 128)) (PreH22 : (rows_well_formed_158 rows words_size_pre )) (PreH23 : (problem_158_pre_z rows )) (PreH24 : (best_prefix_state_158 rows i best_idx maxu )) (PreH25 : (count_scan_state_158 (Znth (i) (rows) ((@nil Z))) j seen_l unique )) ,
  (IntArray.full ( &( "seen" ) ) 128 seen_l )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "words_size" ) )) # Int  |-> words_size_pre)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "max" ) )) # Ptr  |-> max)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "best_idx" ) )) # Int  |-> best_idx)
  **  ((( &( "maxu" ) )) # Int  |-> maxu)
  **  ((( &( "unique" ) )) # Int  |-> unique)
  **  (CharPtrArray2.missing_i words_pre words_size_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition find_max_safety_wit_27 := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (seen_l: (@list Z)) (j: Z) (len: Z) (i: Z) (max: Z) (k: Z) (cmp: Z) (ch: Z) (best_idx: Z) (maxu: Z) (unique: Z) (PreH1 : ((Znth ch seen_l 0) = 0)) (PreH2 : (0 <= (Zlength ((Znth (i) (rows) ((@nil Z))))))) (PreH3 : (0 <= j)) (PreH4 : (j < len)) (PreH5 : (0 <= i)) (PreH6 : (i < words_size_pre)) (PreH7 : (0 < words_size_pre)) (PreH8 : (words_size_pre <= 100)) (PreH9 : (0 <= ch)) (PreH10 : (ch < 128)) (PreH11 : (ch = (Znth (j) ((Znth (i) (rows) ((@nil Z)))) (0)))) (PreH12 : (0 <= best_idx)) (PreH13 : (best_idx < words_size_pre)) (PreH14 : (0 <= maxu)) (PreH15 : (maxu <= 128)) (PreH16 : (0 <= unique)) (PreH17 : (unique <= 128)) (PreH18 : (len = (string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))))) (PreH19 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = (len + 1 ))) (PreH20 : (valid_string (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) )) (PreH21 : ((Zlength (seen_l)) = 128)) (PreH22 : (rows_well_formed_158 rows words_size_pre )) (PreH23 : (problem_158_pre_z rows )) (PreH24 : (best_prefix_state_158 rows i best_idx maxu )) (PreH25 : (count_scan_state_158 (Znth (i) (rows) ((@nil Z))) j seen_l unique )) ,
  (IntArray.full ( &( "seen" ) ) 128 (replace_Znth (ch) (1) (seen_l)) )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "words_size" ) )) # Int  |-> words_size_pre)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "max" ) )) # Ptr  |-> max)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "best_idx" ) )) # Int  |-> best_idx)
  **  ((( &( "maxu" ) )) # Int  |-> maxu)
  **  ((( &( "unique" ) )) # Int  |-> unique)
  **  (CharPtrArray2.missing_i words_pre words_size_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
|--
  “ ((unique + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (unique + 1 )) ”
.

Definition find_max_safety_wit_28 := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (seen_l: (@list Z)) (j: Z) (len: Z) (i: Z) (max: Z) (k: Z) (cmp: Z) (ch: Z) (best_idx: Z) (maxu: Z) (unique: Z) (PreH1 : ((Znth ch seen_l 0) = 0)) (PreH2 : (0 <= (Zlength ((Znth (i) (rows) ((@nil Z))))))) (PreH3 : (0 <= j)) (PreH4 : (j < len)) (PreH5 : (0 <= i)) (PreH6 : (i < words_size_pre)) (PreH7 : (0 < words_size_pre)) (PreH8 : (words_size_pre <= 100)) (PreH9 : (0 <= ch)) (PreH10 : (ch < 128)) (PreH11 : (ch = (Znth (j) ((Znth (i) (rows) ((@nil Z)))) (0)))) (PreH12 : (0 <= best_idx)) (PreH13 : (best_idx < words_size_pre)) (PreH14 : (0 <= maxu)) (PreH15 : (maxu <= 128)) (PreH16 : (0 <= unique)) (PreH17 : (unique <= 128)) (PreH18 : (len = (string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))))) (PreH19 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = (len + 1 ))) (PreH20 : (valid_string (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) )) (PreH21 : ((Zlength (seen_l)) = 128)) (PreH22 : (rows_well_formed_158 rows words_size_pre )) (PreH23 : (problem_158_pre_z rows )) (PreH24 : (best_prefix_state_158 rows i best_idx maxu )) (PreH25 : (count_scan_state_158 (Znth (i) (rows) ((@nil Z))) j seen_l unique )) ,
  (IntArray.full ( &( "seen" ) ) 128 (replace_Znth (ch) (1) (seen_l)) )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "words_size" ) )) # Int  |-> words_size_pre)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "max" ) )) # Ptr  |-> max)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "best_idx" ) )) # Int  |-> best_idx)
  **  ((( &( "maxu" ) )) # Int  |-> maxu)
  **  ((( &( "unique" ) )) # Int  |-> unique)
  **  (CharPtrArray2.missing_i words_pre words_size_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition find_max_safety_wit_29 := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (seen_l: (@list Z)) (j: Z) (len: Z) (i: Z) (max: Z) (k: Z) (cmp: Z) (ch: Z) (best_idx: Z) (maxu: Z) (unique: Z) (PreH1 : ((Znth ch seen_l 0) = 0)) (PreH2 : (0 <= (Zlength ((Znth (i) (rows) ((@nil Z))))))) (PreH3 : (0 <= j)) (PreH4 : (j < len)) (PreH5 : (0 <= i)) (PreH6 : (i < words_size_pre)) (PreH7 : (0 < words_size_pre)) (PreH8 : (words_size_pre <= 100)) (PreH9 : (0 <= ch)) (PreH10 : (ch < 128)) (PreH11 : (ch = (Znth (j) ((Znth (i) (rows) ((@nil Z)))) (0)))) (PreH12 : (0 <= best_idx)) (PreH13 : (best_idx < words_size_pre)) (PreH14 : (0 <= maxu)) (PreH15 : (maxu <= 128)) (PreH16 : (0 <= unique)) (PreH17 : (unique <= 128)) (PreH18 : (len = (string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))))) (PreH19 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = (len + 1 ))) (PreH20 : (valid_string (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) )) (PreH21 : ((Zlength (seen_l)) = 128)) (PreH22 : (rows_well_formed_158 rows words_size_pre )) (PreH23 : (problem_158_pre_z rows )) (PreH24 : (best_prefix_state_158 rows i best_idx maxu )) (PreH25 : (count_scan_state_158 (Znth (i) (rows) ((@nil Z))) j seen_l unique )) ,
  (IntArray.full ( &( "seen" ) ) 128 (replace_Znth (ch) (1) (seen_l)) )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "words_size" ) )) # Int  |-> words_size_pre)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "max" ) )) # Ptr  |-> max)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "best_idx" ) )) # Int  |-> best_idx)
  **  ((( &( "maxu" ) )) # Int  |-> maxu)
  **  ((( &( "unique" ) )) # Int  |-> (unique + 1 ))
  **  (CharPtrArray2.missing_i words_pre words_size_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition find_max_safety_wit_30 := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (seen_l: (@list Z)) (j: Z) (len: Z) (i: Z) (max: Z) (k: Z) (cmp: Z) (ch: Z) (best_idx: Z) (maxu: Z) (unique: Z) (PreH1 : ((Znth ch seen_l 0) = 0)) (PreH2 : (0 <= (Zlength ((Znth (i) (rows) ((@nil Z))))))) (PreH3 : (0 <= j)) (PreH4 : (j < len)) (PreH5 : (0 <= i)) (PreH6 : (i < words_size_pre)) (PreH7 : (0 < words_size_pre)) (PreH8 : (words_size_pre <= 100)) (PreH9 : (0 <= ch)) (PreH10 : (ch < 128)) (PreH11 : (ch = (Znth (j) ((Znth (i) (rows) ((@nil Z)))) (0)))) (PreH12 : (0 <= best_idx)) (PreH13 : (best_idx < words_size_pre)) (PreH14 : (0 <= maxu)) (PreH15 : (maxu <= 128)) (PreH16 : (0 <= unique)) (PreH17 : (unique <= 128)) (PreH18 : (len = (string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))))) (PreH19 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = (len + 1 ))) (PreH20 : (valid_string (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) )) (PreH21 : ((Zlength (seen_l)) = 128)) (PreH22 : (rows_well_formed_158 rows words_size_pre )) (PreH23 : (problem_158_pre_z rows )) (PreH24 : (best_prefix_state_158 rows i best_idx maxu )) (PreH25 : (count_scan_state_158 (Znth (i) (rows) ((@nil Z))) j seen_l unique )) ,
  (IntArray.full ( &( "seen" ) ) 128 (replace_Znth (ch) (1) (seen_l)) )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "words_size" ) )) # Int  |-> words_size_pre)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "max" ) )) # Ptr  |-> max)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "best_idx" ) )) # Int  |-> best_idx)
  **  ((( &( "maxu" ) )) # Int  |-> maxu)
  **  ((( &( "unique" ) )) # Int  |-> (unique + 1 ))
  **  (CharPtrArray2.missing_i words_pre words_size_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition find_max_safety_wit_31 := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (seen_l: (@list Z)) (j: Z) (len: Z) (i: Z) (max: Z) (k: Z) (cmp: Z) (ch: Z) (best_idx: Z) (maxu: Z) (unique: Z) (PreH1 : ((Znth ch seen_l 0) <> 0)) (PreH2 : (0 <= (Zlength ((Znth (i) (rows) ((@nil Z))))))) (PreH3 : (0 <= j)) (PreH4 : (j < len)) (PreH5 : (0 <= i)) (PreH6 : (i < words_size_pre)) (PreH7 : (0 < words_size_pre)) (PreH8 : (words_size_pre <= 100)) (PreH9 : (0 <= ch)) (PreH10 : (ch < 128)) (PreH11 : (ch = (Znth (j) ((Znth (i) (rows) ((@nil Z)))) (0)))) (PreH12 : (0 <= best_idx)) (PreH13 : (best_idx < words_size_pre)) (PreH14 : (0 <= maxu)) (PreH15 : (maxu <= 128)) (PreH16 : (0 <= unique)) (PreH17 : (unique <= 128)) (PreH18 : (len = (string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))))) (PreH19 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = (len + 1 ))) (PreH20 : (valid_string (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) )) (PreH21 : ((Zlength (seen_l)) = 128)) (PreH22 : (rows_well_formed_158 rows words_size_pre )) (PreH23 : (problem_158_pre_z rows )) (PreH24 : (best_prefix_state_158 rows i best_idx maxu )) (PreH25 : (count_scan_state_158 (Znth (i) (rows) ((@nil Z))) j seen_l unique )) ,
  (IntArray.full ( &( "seen" ) ) 128 seen_l )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "words_size" ) )) # Int  |-> words_size_pre)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "max" ) )) # Ptr  |-> max)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "best_idx" ) )) # Int  |-> best_idx)
  **  ((( &( "maxu" ) )) # Int  |-> maxu)
  **  ((( &( "unique" ) )) # Int  |-> unique)
  **  (CharPtrArray2.missing_i words_pre words_size_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition find_max_safety_wit_32 := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (seen_l: (@list Z)) (j: Z) (len: Z) (i: Z) (max: Z) (k: Z) (cmp: Z) (ch: Z) (best_idx: Z) (maxu: Z) (unique: Z) (PreH1 : ((Znth ch seen_l 0) <> 0)) (PreH2 : (0 <= (Zlength ((Znth (i) (rows) ((@nil Z))))))) (PreH3 : (0 <= j)) (PreH4 : (j < len)) (PreH5 : (0 <= i)) (PreH6 : (i < words_size_pre)) (PreH7 : (0 < words_size_pre)) (PreH8 : (words_size_pre <= 100)) (PreH9 : (0 <= ch)) (PreH10 : (ch < 128)) (PreH11 : (ch = (Znth (j) ((Znth (i) (rows) ((@nil Z)))) (0)))) (PreH12 : (0 <= best_idx)) (PreH13 : (best_idx < words_size_pre)) (PreH14 : (0 <= maxu)) (PreH15 : (maxu <= 128)) (PreH16 : (0 <= unique)) (PreH17 : (unique <= 128)) (PreH18 : (len = (string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))))) (PreH19 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = (len + 1 ))) (PreH20 : (valid_string (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) )) (PreH21 : ((Zlength (seen_l)) = 128)) (PreH22 : (rows_well_formed_158 rows words_size_pre )) (PreH23 : (problem_158_pre_z rows )) (PreH24 : (best_prefix_state_158 rows i best_idx maxu )) (PreH25 : (count_scan_state_158 (Znth (i) (rows) ((@nil Z))) j seen_l unique )) ,
  (IntArray.full ( &( "seen" ) ) 128 seen_l )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "words_size" ) )) # Int  |-> words_size_pre)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "max" ) )) # Ptr  |-> max)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "best_idx" ) )) # Int  |-> best_idx)
  **  ((( &( "maxu" ) )) # Int  |-> maxu)
  **  ((( &( "unique" ) )) # Int  |-> unique)
  **  (CharPtrArray2.missing_i words_pre words_size_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition find_max_safety_wit_33 := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (best_ptr: Z) (seen_l: (@list Z)) (i: Z) (best_idx: Z) (k: Z) (j: Z) (unique: Z) (maxu: Z) (cmp: Z) (len_addr_v: Z) (ch_addr_v: Z) (PreH1 : (0 <= i)) (PreH2 : (i < words_size_pre)) (PreH3 : (0 < words_size_pre)) (PreH4 : (words_size_pre <= 100)) (PreH5 : (0 <= best_idx)) (PreH6 : (best_idx < words_size_pre)) (PreH7 : (i <> best_idx)) (PreH8 : (unique = (row_unique_count_z_158 ((Znth (i) (rows) ((@nil Z))))))) (PreH9 : (unique = maxu)) (PreH10 : (0 <= maxu)) (PreH11 : (maxu <= 128)) (PreH12 : (0 <= unique)) (PreH13 : (unique <= 128)) (PreH14 : (rows_well_formed_158 rows words_size_pre )) (PreH15 : (problem_158_pre_z rows )) (PreH16 : (best_prefix_state_158 rows i best_idx maxu )) (PreH17 : (valid_string (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) )) (PreH18 : (valid_string (row_payload_z_158 ((Znth (best_idx) (rows) ((@nil Z))))) )) (PreH19 : ((string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX)) (PreH20 : ((string_length ((row_payload_z_158 ((Znth (best_idx) (rows) ((@nil Z))))))) < INT_MAX)) (PreH21 : (strcmp_result (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) (row_payload_z_158 ((Znth (best_idx) (rows) ((@nil Z))))) cmp )) (PreH22 : ((Zlength (seen_l)) = 128)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best_idx" ) )) # Int  |-> best_idx)
  **  ((( &( "words_size" ) )) # Int  |-> words_size_pre)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "max" ) )) # Ptr  |-> best_ptr)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "unique" ) )) # Int  |-> unique)
  **  ((( &( "maxu" ) )) # Int  |-> maxu)
  **  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  (char_ptr_array2_missing_two_158 words_pre words_size_pre i row_ptr best_idx best_ptr rows )
  **  (store_string row_ptr (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) )
  **  (((words_pre + (best_idx * sizeof(PTR) ) )) # Ptr  |-> best_ptr)
  **  (store_string best_ptr (row_payload_z_158 ((Znth (best_idx) (rows) ((@nil Z))))) )
  **  ((( &( "len" ) )) # Int  |-> len_addr_v)
  **  ((( &( "ch" ) )) # Int  |-> ch_addr_v)
  **  (IntArray.full ( &( "seen" ) ) 128 seen_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition find_max_safety_wit_34 := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (seen_l: (@list Z)) (i: Z) (max: Z) (cur: Z) (j: Z) (cmp: Z) (len: Z) (ch: Z) (best_idx: Z) (maxu: Z) (unique: Z) (k_addr_v: Z) (PreH1 : (0 <= i)) (PreH2 : (i < words_size_pre)) (PreH3 : (0 < words_size_pre)) (PreH4 : (words_size_pre <= 100)) (PreH5 : (0 <= best_idx)) (PreH6 : (best_idx < words_size_pre)) (PreH7 : (0 <= maxu)) (PreH8 : (maxu <= 128)) (PreH9 : (0 <= unique)) (PreH10 : (unique <= 128)) (PreH11 : (rows_well_formed_158 rows words_size_pre )) (PreH12 : (problem_158_pre_z rows )) (PreH13 : (best_prefix_state_158 rows (i + 1 ) best_idx maxu )) (PreH14 : ((Zlength (seen_l)) = 128)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "words_size" ) )) # Int  |-> words_size_pre)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "max" ) )) # Ptr  |-> max)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "best_idx" ) )) # Int  |-> best_idx)
  **  ((( &( "maxu" ) )) # Int  |-> maxu)
  **  ((( &( "unique" ) )) # Int  |-> unique)
  **  (CharPtrArray2.full words_pre words_size_pre rows )
  **  ((( &( "k" ) )) # Int  |-> k_addr_v)
  **  (IntArray.full ( &( "seen" ) ) 128 seen_l )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition find_max_safety_wit_35 := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (seen_l: (@list Z)) (i: Z) (max: Z) (cur: Z) (j: Z) (cmp: Z) (len: Z) (ch: Z) (best_idx: Z) (maxu: Z) (unique: Z) (k_addr_v: Z) (PreH1 : (0 <= i)) (PreH2 : (i < words_size_pre)) (PreH3 : (0 < words_size_pre)) (PreH4 : (words_size_pre <= 100)) (PreH5 : (0 <= best_idx)) (PreH6 : (best_idx < words_size_pre)) (PreH7 : (0 <= maxu)) (PreH8 : (maxu <= 128)) (PreH9 : (0 <= unique)) (PreH10 : (unique <= 128)) (PreH11 : (rows_well_formed_158 rows words_size_pre )) (PreH12 : (problem_158_pre_z rows )) (PreH13 : (best_prefix_state_158 rows (i + 1 ) best_idx maxu )) (PreH14 : ((Zlength (seen_l)) = 128)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "words_size" ) )) # Int  |-> words_size_pre)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "max" ) )) # Ptr  |-> max)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "best_idx" ) )) # Int  |-> best_idx)
  **  ((( &( "maxu" ) )) # Int  |-> maxu)
  **  ((( &( "unique" ) )) # Int  |-> unique)
  **  (CharPtrArray2.full words_pre words_size_pre rows )
  **  ((( &( "k" ) )) # Int  |-> k_addr_v)
  **  (IntArray.full ( &( "seen" ) ) 128 seen_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition find_max_entail_wit_1 := 
(
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z)))  __default__List_Z (PreH1 : (0 <= (Zlength ((Znth 0 rows __default__List_Z))))) (PreH2 : (0 < words_size_pre)) (PreH3 : (words_size_pre <= 100)) (PreH4 : (rows_well_formed_158 rows words_size_pre )) (PreH5 : (problem_158_pre_z rows )) ,
  (CharPtrArray2.full words_pre words_size_pre rows )
  **  (IntArray.undef_full ( &( "seen" ) ) 128 )
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= 128) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 < words_size_pre) ” 
  &&  “ (words_size_pre <= 100) ” 
  &&  “ (rows_well_formed_158 rows words_size_pre ) ” 
  &&  “ (problem_158_pre_z rows ) ”
  &&  (CharPtrArray2.full words_pre words_size_pre rows )
  **  (IntArray.seg ( &( "seen" ) ) 0 0 (zeros (0)) )
  **  (IntArray.undef_seg ( &( "seen" ) ) 0 128 )
) \/
(
forall (words_size_pre: Z) (rows: (@list (@list Z)))  __default__List_Z (PreH1 : (0 <= (Zlength ((Znth 0 rows __default__List_Z))))) (PreH2 : (0 < words_size_pre)) (PreH3 : (words_size_pre <= 100)) (PreH4 : (rows_well_formed_158 rows words_size_pre )) (PreH5 : (problem_158_pre_z rows )) ,
  TT && emp 
|--
  “ ((zeros (0)) = (@nil Z)) ”
  &&  emp
).

Definition find_max_entail_wit_1_split_goal_1 := 
forall (words_size_pre: Z) (rows: (@list (@list Z)))  __default__List_Z (PreH1 : (0 <= (Zlength ((Znth 0 rows __default__List_Z))))) (PreH2 : (0 < words_size_pre)) (PreH3 : (words_size_pre <= 100)) (PreH4 : (rows_well_formed_158 rows words_size_pre )) (PreH5 : (problem_158_pre_z rows )) ,
  TT && emp 
|--
  “ ((zeros (0)) = (@nil Z)) ”
.

Definition find_max_entail_wit_2 := 
(
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (best_idx: Z) (unique: Z) (maxu: Z) (ch: Z) (len: Z) (j: Z) (k: Z) (PreH1 : (k < 128)) (PreH2 : (0 <= k)) (PreH3 : (k <= 128)) (PreH4 : (j = 0)) (PreH5 : (len = 0)) (PreH6 : (ch = 0)) (PreH7 : (maxu = 0)) (PreH8 : (unique = 0)) (PreH9 : (best_idx = 0)) (PreH10 : (0 < words_size_pre)) (PreH11 : (words_size_pre <= 100)) (PreH12 : (rows_well_formed_158 rows words_size_pre )) (PreH13 : (problem_158_pre_z rows )) ,
  (IntArray.seg ( &( "seen" ) ) 0 (k + 1 ) (app ((zeros (k))) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "seen" ) ) (k + 1 ) 128 )
  **  (CharPtrArray2.full words_pre words_size_pre rows )
|--
  “ (0 <= (k + 1 )) ” 
  &&  “ ((k + 1 ) <= 128) ” 
  &&  “ (j = 0) ” 
  &&  “ (len = 0) ” 
  &&  “ (ch = 0) ” 
  &&  “ (maxu = 0) ” 
  &&  “ (unique = 0) ” 
  &&  “ (best_idx = 0) ” 
  &&  “ (0 < words_size_pre) ” 
  &&  “ (words_size_pre <= 100) ” 
  &&  “ (rows_well_formed_158 rows words_size_pre ) ” 
  &&  “ (problem_158_pre_z rows ) ”
  &&  (CharPtrArray2.full words_pre words_size_pre rows )
  **  (IntArray.seg ( &( "seen" ) ) 0 (k + 1 ) (zeros ((k + 1 ))) )
  **  (IntArray.undef_seg ( &( "seen" ) ) (k + 1 ) 128 )
) \/
(
forall (words_size_pre: Z) (rows: (@list (@list Z))) (best_idx: Z) (unique: Z) (maxu: Z) (ch: Z) (len: Z) (j: Z) (k: Z) (PreH1 : (k < 128)) (PreH2 : (0 <= k)) (PreH3 : (k <= 128)) (PreH4 : (j = 0)) (PreH5 : (len = 0)) (PreH6 : (ch = 0)) (PreH7 : (maxu = 0)) (PreH8 : (unique = 0)) (PreH9 : (best_idx = 0)) (PreH10 : (0 < words_size_pre)) (PreH11 : (words_size_pre <= 100)) (PreH12 : (rows_well_formed_158 rows words_size_pre )) (PreH13 : (problem_158_pre_z rows )) ,
  TT && emp 
|--
  “ ((app ((zeros (k))) ((cons (0) ((@nil Z))))) = (zeros ((k + 1 )))) ”
  &&  emp
).

Definition find_max_entail_wit_2_split_goal_1 := 
forall (words_size_pre: Z) (rows: (@list (@list Z))) (best_idx: Z) (unique: Z) (maxu: Z) (ch: Z) (len: Z) (j: Z) (k: Z) (PreH1 : (k < 128)) (PreH2 : (0 <= k)) (PreH3 : (k <= 128)) (PreH4 : (j = 0)) (PreH5 : (len = 0)) (PreH6 : (ch = 0)) (PreH7 : (maxu = 0)) (PreH8 : (unique = 0)) (PreH9 : (best_idx = 0)) (PreH10 : (0 < words_size_pre)) (PreH11 : (words_size_pre <= 100)) (PreH12 : (rows_well_formed_158 rows words_size_pre )) (PreH13 : (problem_158_pre_z rows )) ,
  TT && emp 
|--
  “ ((app ((zeros (k))) ((cons (0) ((@nil Z))))) = (zeros ((k + 1 )))) ”
.

Definition find_max_entail_wit_3 := 
(
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (best_idx: Z) (unique: Z) (maxu: Z) (ch: Z) (len: Z) (j: Z) (k: Z) (PreH1 : (k >= 128)) (PreH2 : (0 <= k)) (PreH3 : (k <= 128)) (PreH4 : (j = 0)) (PreH5 : (len = 0)) (PreH6 : (ch = 0)) (PreH7 : (maxu = 0)) (PreH8 : (unique = 0)) (PreH9 : (best_idx = 0)) (PreH10 : (0 < words_size_pre)) (PreH11 : (words_size_pre <= 100)) (PreH12 : (rows_well_formed_158 rows words_size_pre )) (PreH13 : (problem_158_pre_z rows )) ,
  (CharPtrArray2.full words_pre words_size_pre rows )
  **  (IntArray.seg ( &( "seen" ) ) 0 k (zeros (k)) )
  **  (IntArray.undef_seg ( &( "seen" ) ) k 128 )
|--
  EX (seen_l: (@list Z)) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= words_size_pre) ” 
  &&  “ (0 < words_size_pre) ” 
  &&  “ (words_size_pre <= 100) ” 
  &&  “ (0 <= best_idx) ” 
  &&  “ (best_idx < words_size_pre) ” 
  &&  “ (0 <= maxu) ” 
  &&  “ (maxu <= 128) ” 
  &&  “ (0 <= unique) ” 
  &&  “ (unique <= 128) ” 
  &&  “ (rows_well_formed_158 rows words_size_pre ) ” 
  &&  “ (problem_158_pre_z rows ) ” 
  &&  “ (best_prefix_state_158 rows 0 best_idx maxu ) ” 
  &&  “ ((Zlength (seen_l)) = 128) ”
  &&  (CharPtrArray2.full words_pre words_size_pre rows )
  **  (IntArray.full ( &( "seen" ) ) 128 seen_l )
) \/
(
forall (words_size_pre: Z) (rows: (@list (@list Z))) (best_idx: Z) (unique: Z) (maxu: Z) (ch: Z) (len: Z) (j: Z) (k: Z) (PreH1 : (k >= 128)) (PreH2 : (0 <= k)) (PreH3 : (k <= 128)) (PreH4 : (j = 0)) (PreH5 : (len = 0)) (PreH6 : (ch = 0)) (PreH7 : (maxu = 0)) (PreH8 : (unique = 0)) (PreH9 : (best_idx = 0)) (PreH10 : (0 < words_size_pre)) (PreH11 : (words_size_pre <= 100)) (PreH12 : (rows_well_formed_158 rows words_size_pre )) (PreH13 : (problem_158_pre_z rows )) ,
  (IntArray.seg ( &( "seen" ) ) 0 k (zeros (k)) )
|--
  EX (seen_l: (@list Z)) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= words_size_pre) ” 
  &&  “ (0 < words_size_pre) ” 
  &&  “ (words_size_pre <= 100) ” 
  &&  “ (0 <= best_idx) ” 
  &&  “ (best_idx < words_size_pre) ” 
  &&  “ (0 <= maxu) ” 
  &&  “ (maxu <= 128) ” 
  &&  “ (0 <= unique) ” 
  &&  “ (unique <= 128) ” 
  &&  “ (rows_well_formed_158 rows words_size_pre ) ” 
  &&  “ (problem_158_pre_z rows ) ” 
  &&  “ (best_prefix_state_158 rows 0 best_idx maxu ) ” 
  &&  “ ((Zlength (seen_l)) = 128) ”
  &&  (IntArray.full ( &( "seen" ) ) 128 seen_l )
).

Definition find_max_entail_wit_4 := 
(
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (seen_l_2: (@list Z)) (unique: Z) (maxu: Z) (best_idx: Z) (i: Z) (PreH1 : (i < words_size_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= words_size_pre)) (PreH4 : (0 < words_size_pre)) (PreH5 : (words_size_pre <= 100)) (PreH6 : (0 <= best_idx)) (PreH7 : (best_idx < words_size_pre)) (PreH8 : (0 <= maxu)) (PreH9 : (maxu <= 128)) (PreH10 : (0 <= unique)) (PreH11 : (unique <= 128)) (PreH12 : (rows_well_formed_158 rows words_size_pre )) (PreH13 : (problem_158_pre_z rows )) (PreH14 : (best_prefix_state_158 rows i best_idx maxu )) (PreH15 : ((Zlength (seen_l_2)) = 128)) ,
  (CharPtrArray2.full words_pre words_size_pre rows )
  **  (IntArray.full ( &( "seen" ) ) 128 seen_l_2 )
|--
  EX (row_ptr: Z)  (seen_l: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i < words_size_pre) ” 
  &&  “ (0 < words_size_pre) ” 
  &&  “ (words_size_pre <= 100) ” 
  &&  “ (0 <= best_idx) ” 
  &&  “ (best_idx < words_size_pre) ” 
  &&  “ (0 <= maxu) ” 
  &&  “ (maxu <= 128) ” 
  &&  “ (0 <= unique) ” 
  &&  “ (unique <= 128) ” 
  &&  “ (rows_well_formed_158 rows words_size_pre ) ” 
  &&  “ (problem_158_pre_z rows ) ” 
  &&  “ (best_prefix_state_158 rows i best_idx maxu ) ” 
  &&  “ ((Zlength (seen_l)) = 128) ”
  &&  (CharPtrArray2.missing_i words_pre words_size_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
  **  (IntArray.full ( &( "seen" ) ) 128 seen_l )
) \/
(
forall (words_size_pre: Z) (rows: (@list (@list Z))) (seen_l_2: (@list Z)) (unique: Z) (maxu: Z) (best_idx: Z) (i: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (0 <= (Zlength ((Znth i rows __default__List_Z))))) (PreH2 : (i < words_size_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= words_size_pre)) (PreH5 : (0 < words_size_pre)) (PreH6 : (words_size_pre <= 100)) (PreH7 : (0 <= best_idx)) (PreH8 : (best_idx < words_size_pre)) (PreH9 : (0 <= maxu)) (PreH10 : (maxu <= 128)) (PreH11 : (0 <= unique)) (PreH12 : (unique <= 128)) (PreH13 : (rows_well_formed_158 rows words_size_pre )) (PreH14 : (problem_158_pre_z rows )) (PreH15 : (best_prefix_state_158 rows i best_idx maxu )) (PreH16 : ((Zlength (seen_l_2)) = 128)) ,
  (CharArray.full row_ptr_2 (Zlength ((Znth i rows __default__List_Z))) (Znth i rows __default__List_Z) )
|--
  (CharArray.full row_ptr_2 (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
).

Definition find_max_entail_wit_4_split_goal_spatial := 
forall (words_size_pre: Z) (rows: (@list (@list Z))) (seen_l_2: (@list Z)) (unique: Z) (maxu: Z) (best_idx: Z) (i: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (0 <= (Zlength ((Znth i rows __default__List_Z))))) (PreH2 : (i < words_size_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= words_size_pre)) (PreH5 : (0 < words_size_pre)) (PreH6 : (words_size_pre <= 100)) (PreH7 : (0 <= best_idx)) (PreH8 : (best_idx < words_size_pre)) (PreH9 : (0 <= maxu)) (PreH10 : (maxu <= 128)) (PreH11 : (0 <= unique)) (PreH12 : (unique <= 128)) (PreH13 : (rows_well_formed_158 rows words_size_pre )) (PreH14 : (problem_158_pre_z rows )) (PreH15 : (best_prefix_state_158 rows i best_idx maxu )) (PreH16 : ((Zlength (seen_l_2)) = 128)) ,
  (CharArray.full row_ptr_2 (Zlength ((Znth i rows __default__List_Z))) (Znth i rows __default__List_Z) )
|--
  (CharArray.full row_ptr_2 (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
.

Definition find_max_entail_wit_5 := 
(
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (row_ptr_2: Z) (seen_l_2: (@list Z)) (i: Z) (best_idx: Z) (maxu: Z) (unique: Z) (PreH1 : (0 <= i)) (PreH2 : (i < words_size_pre)) (PreH3 : (0 < words_size_pre)) (PreH4 : (words_size_pre <= 100)) (PreH5 : (0 <= best_idx)) (PreH6 : (best_idx < words_size_pre)) (PreH7 : (0 <= maxu)) (PreH8 : (maxu <= 128)) (PreH9 : (0 <= unique)) (PreH10 : (unique <= 128)) (PreH11 : (rows_well_formed_158 rows words_size_pre )) (PreH12 : (problem_158_pre_z rows )) (PreH13 : (best_prefix_state_158 rows i best_idx maxu )) (PreH14 : ((Zlength (seen_l_2)) = 128)) ,
  (CharPtrArray2.missing_i words_pre words_size_pre i row_ptr_2 rows )
  **  (((words_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr_2)
  **  (CharArray.full row_ptr_2 (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
  **  (IntArray.full ( &( "seen" ) ) 128 seen_l_2 )
|--
  EX (row_ptr: Z)  (seen_l: (@list Z)) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= 128) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < words_size_pre) ” 
  &&  “ (0 < words_size_pre) ” 
  &&  “ (words_size_pre <= 100) ” 
  &&  “ (0 <= best_idx) ” 
  &&  “ (best_idx < words_size_pre) ” 
  &&  “ (0 <= maxu) ” 
  &&  “ (maxu <= 128) ” 
  &&  “ (0 <= unique) ” 
  &&  “ (unique <= 128) ” 
  &&  “ (rows_well_formed_158 rows words_size_pre ) ” 
  &&  “ (problem_158_pre_z rows ) ” 
  &&  “ (best_prefix_state_158 rows i best_idx maxu ) ” 
  &&  “ ((Zlength (seen_l)) = 128) ” 
  &&  “ (reset_prefix_state_158 0 seen_l ) ”
  &&  (CharPtrArray2.missing_i words_pre words_size_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
  **  (IntArray.full ( &( "seen" ) ) 128 seen_l )
) \/
(
forall (words_size_pre: Z) (rows: (@list (@list Z))) (seen_l_2: (@list Z)) (i: Z) (best_idx: Z) (maxu: Z) (unique: Z) (PreH1 : (0 <= (Zlength ((Znth (i) (rows) ((@nil Z))))))) (PreH2 : (0 <= i)) (PreH3 : (i < words_size_pre)) (PreH4 : (0 < words_size_pre)) (PreH5 : (words_size_pre <= 100)) (PreH6 : (0 <= best_idx)) (PreH7 : (best_idx < words_size_pre)) (PreH8 : (0 <= maxu)) (PreH9 : (maxu <= 128)) (PreH10 : (0 <= unique)) (PreH11 : (unique <= 128)) (PreH12 : (rows_well_formed_158 rows words_size_pre )) (PreH13 : (problem_158_pre_z rows )) (PreH14 : (best_prefix_state_158 rows i best_idx maxu )) (PreH15 : ((Zlength (seen_l_2)) = 128)) ,
  TT && emp 
|--
  “ (reset_prefix_state_158 0 seen_l_2 ) ”
  &&  emp
).

Definition find_max_entail_wit_5_split_goal_1 := 
forall (words_size_pre: Z) (rows: (@list (@list Z))) (seen_l_2: (@list Z)) (i: Z) (best_idx: Z) (maxu: Z) (unique: Z) (PreH1 : (0 <= (Zlength ((Znth (i) (rows) ((@nil Z))))))) (PreH2 : (0 <= i)) (PreH3 : (i < words_size_pre)) (PreH4 : (0 < words_size_pre)) (PreH5 : (words_size_pre <= 100)) (PreH6 : (0 <= best_idx)) (PreH7 : (best_idx < words_size_pre)) (PreH8 : (0 <= maxu)) (PreH9 : (maxu <= 128)) (PreH10 : (0 <= unique)) (PreH11 : (unique <= 128)) (PreH12 : (rows_well_formed_158 rows words_size_pre )) (PreH13 : (problem_158_pre_z rows )) (PreH14 : (best_prefix_state_158 rows i best_idx maxu )) (PreH15 : ((Zlength (seen_l_2)) = 128)) ,
  TT && emp 
|--
  “ (reset_prefix_state_158 0 seen_l_2 ) ”
.

Definition find_max_entail_wit_6 := 
(
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (row_ptr_2: Z) (seen_l_2: (@list Z)) (unique: Z) (maxu: Z) (best_idx: Z) (i: Z) (k: Z) (PreH1 : (0 <= (Zlength ((Znth (i) (rows) ((@nil Z))))))) (PreH2 : (k < 128)) (PreH3 : (0 <= k)) (PreH4 : (k <= 128)) (PreH5 : (0 <= i)) (PreH6 : (i < words_size_pre)) (PreH7 : (0 < words_size_pre)) (PreH8 : (words_size_pre <= 100)) (PreH9 : (0 <= best_idx)) (PreH10 : (best_idx < words_size_pre)) (PreH11 : (0 <= maxu)) (PreH12 : (maxu <= 128)) (PreH13 : (0 <= unique)) (PreH14 : (unique <= 128)) (PreH15 : (rows_well_formed_158 rows words_size_pre )) (PreH16 : (problem_158_pre_z rows )) (PreH17 : (best_prefix_state_158 rows i best_idx maxu )) (PreH18 : ((Zlength (seen_l_2)) = 128)) (PreH19 : (reset_prefix_state_158 k seen_l_2 )) ,
  (IntArray.full ( &( "seen" ) ) 128 (replace_Znth (k) (0) (seen_l_2)) )
  **  (CharPtrArray2.missing_i words_pre words_size_pre i row_ptr_2 rows )
  **  (((words_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr_2)
  **  (CharArray.full row_ptr_2 (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
|--
  EX (row_ptr: Z)  (seen_l: (@list Z)) ,
  “ (0 <= (k + 1 )) ” 
  &&  “ ((k + 1 ) <= 128) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < words_size_pre) ” 
  &&  “ (0 < words_size_pre) ” 
  &&  “ (words_size_pre <= 100) ” 
  &&  “ (0 <= best_idx) ” 
  &&  “ (best_idx < words_size_pre) ” 
  &&  “ (0 <= maxu) ” 
  &&  “ (maxu <= 128) ” 
  &&  “ (0 <= unique) ” 
  &&  “ (unique <= 128) ” 
  &&  “ (rows_well_formed_158 rows words_size_pre ) ” 
  &&  “ (problem_158_pre_z rows ) ” 
  &&  “ (best_prefix_state_158 rows i best_idx maxu ) ” 
  &&  “ ((Zlength (seen_l)) = 128) ” 
  &&  “ (reset_prefix_state_158 (k + 1 ) seen_l ) ”
  &&  (CharPtrArray2.missing_i words_pre words_size_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
  **  (IntArray.full ( &( "seen" ) ) 128 seen_l )
) \/
(
forall (words_size_pre: Z) (rows: (@list (@list Z))) (seen_l_2: (@list Z)) (unique: Z) (maxu: Z) (best_idx: Z) (i: Z) (k: Z) (PreH1 : (0 <= (Zlength ((Znth (i) (rows) ((@nil Z))))))) (PreH2 : (k < 128)) (PreH3 : (0 <= k)) (PreH4 : (k <= 128)) (PreH5 : (0 <= i)) (PreH6 : (i < words_size_pre)) (PreH7 : (0 < words_size_pre)) (PreH8 : (words_size_pre <= 100)) (PreH9 : (0 <= best_idx)) (PreH10 : (best_idx < words_size_pre)) (PreH11 : (0 <= maxu)) (PreH12 : (maxu <= 128)) (PreH13 : (0 <= unique)) (PreH14 : (unique <= 128)) (PreH15 : (rows_well_formed_158 rows words_size_pre )) (PreH16 : (problem_158_pre_z rows )) (PreH17 : (best_prefix_state_158 rows i best_idx maxu )) (PreH18 : ((Zlength (seen_l_2)) = 128)) (PreH19 : (reset_prefix_state_158 k seen_l_2 )) ,
  TT && emp 
|--
  “ (reset_prefix_state_158 (k + 1 ) (replace_Znth (k) (0) (seen_l_2)) ) ” 
  &&  “ ((Zlength ((replace_Znth (k) (0) (seen_l_2)))) = 128) ”
  &&  emp
).

Definition find_max_entail_wit_6_split_goal_1 := 
forall (words_size_pre: Z) (rows: (@list (@list Z))) (seen_l_2: (@list Z)) (unique: Z) (maxu: Z) (best_idx: Z) (i: Z) (k: Z) (PreH1 : (0 <= (Zlength ((Znth (i) (rows) ((@nil Z))))))) (PreH2 : (k < 128)) (PreH3 : (0 <= k)) (PreH4 : (k <= 128)) (PreH5 : (0 <= i)) (PreH6 : (i < words_size_pre)) (PreH7 : (0 < words_size_pre)) (PreH8 : (words_size_pre <= 100)) (PreH9 : (0 <= best_idx)) (PreH10 : (best_idx < words_size_pre)) (PreH11 : (0 <= maxu)) (PreH12 : (maxu <= 128)) (PreH13 : (0 <= unique)) (PreH14 : (unique <= 128)) (PreH15 : (rows_well_formed_158 rows words_size_pre )) (PreH16 : (problem_158_pre_z rows )) (PreH17 : (best_prefix_state_158 rows i best_idx maxu )) (PreH18 : ((Zlength (seen_l_2)) = 128)) (PreH19 : (reset_prefix_state_158 k seen_l_2 )) ,
  TT && emp 
|--
  “ (reset_prefix_state_158 (k + 1 ) (replace_Znth (k) (0) (seen_l_2)) ) ”
.

Definition find_max_entail_wit_6_split_goal_2 := 
forall (words_size_pre: Z) (rows: (@list (@list Z))) (seen_l_2: (@list Z)) (unique: Z) (maxu: Z) (best_idx: Z) (i: Z) (k: Z) (PreH1 : (0 <= (Zlength ((Znth (i) (rows) ((@nil Z))))))) (PreH2 : (k < 128)) (PreH3 : (0 <= k)) (PreH4 : (k <= 128)) (PreH5 : (0 <= i)) (PreH6 : (i < words_size_pre)) (PreH7 : (0 < words_size_pre)) (PreH8 : (words_size_pre <= 100)) (PreH9 : (0 <= best_idx)) (PreH10 : (best_idx < words_size_pre)) (PreH11 : (0 <= maxu)) (PreH12 : (maxu <= 128)) (PreH13 : (0 <= unique)) (PreH14 : (unique <= 128)) (PreH15 : (rows_well_formed_158 rows words_size_pre )) (PreH16 : (problem_158_pre_z rows )) (PreH17 : (best_prefix_state_158 rows i best_idx maxu )) (PreH18 : ((Zlength (seen_l_2)) = 128)) (PreH19 : (reset_prefix_state_158 k seen_l_2 )) ,
  TT && emp 
|--
  “ ((Zlength ((replace_Znth (k) (0) (seen_l_2)))) = 128) ”
.

Definition find_max_entail_wit_7 := 
(
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (row_ptr_2: Z) (seen_l: (@list Z)) (unique: Z) (maxu: Z) (best_idx: Z) (i: Z) (k: Z) (PreH1 : (k >= 128)) (PreH2 : (0 <= k)) (PreH3 : (k <= 128)) (PreH4 : (0 <= i)) (PreH5 : (i < words_size_pre)) (PreH6 : (0 < words_size_pre)) (PreH7 : (words_size_pre <= 100)) (PreH8 : (0 <= best_idx)) (PreH9 : (best_idx < words_size_pre)) (PreH10 : (0 <= maxu)) (PreH11 : (maxu <= 128)) (PreH12 : (0 <= unique)) (PreH13 : (unique <= 128)) (PreH14 : (rows_well_formed_158 rows words_size_pre )) (PreH15 : (problem_158_pre_z rows )) (PreH16 : (best_prefix_state_158 rows i best_idx maxu )) (PreH17 : ((Zlength (seen_l)) = 128)) (PreH18 : (reset_prefix_state_158 k seen_l )) ,
  (CharPtrArray2.missing_i words_pre words_size_pre i row_ptr_2 rows )
  **  (((words_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr_2)
  **  (CharArray.full row_ptr_2 (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
  **  (IntArray.full ( &( "seen" ) ) 128 seen_l )
|--
  EX (row_ptr: Z) ,
  “ (0 <= i) ” 
  &&  “ (i < words_size_pre) ” 
  &&  “ (0 < words_size_pre) ” 
  &&  “ (words_size_pre <= 100) ” 
  &&  “ (0 <= best_idx) ” 
  &&  “ (best_idx < words_size_pre) ” 
  &&  “ (0 <= maxu) ” 
  &&  “ (maxu <= 128) ” 
  &&  “ (0 <= unique) ” 
  &&  “ (unique <= 128) ” 
  &&  “ (rows_well_formed_158 rows words_size_pre ) ” 
  &&  “ (problem_158_pre_z rows ) ” 
  &&  “ (best_prefix_state_158 rows i best_idx maxu ) ”
  &&  (IntArray.full ( &( "seen" ) ) 128 (zeros (128)) )
  **  (CharPtrArray2.missing_i words_pre words_size_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
) \/
(
forall (words_size_pre: Z) (rows: (@list (@list Z))) (seen_l: (@list Z)) (unique: Z) (maxu: Z) (best_idx: Z) (i: Z) (k: Z) (PreH1 : (0 <= (Zlength ((Znth (i) (rows) ((@nil Z))))))) (PreH2 : (k >= 128)) (PreH3 : (0 <= k)) (PreH4 : (k <= 128)) (PreH5 : (0 <= i)) (PreH6 : (i < words_size_pre)) (PreH7 : (0 < words_size_pre)) (PreH8 : (words_size_pre <= 100)) (PreH9 : (0 <= best_idx)) (PreH10 : (best_idx < words_size_pre)) (PreH11 : (0 <= maxu)) (PreH12 : (maxu <= 128)) (PreH13 : (0 <= unique)) (PreH14 : (unique <= 128)) (PreH15 : (rows_well_formed_158 rows words_size_pre )) (PreH16 : (problem_158_pre_z rows )) (PreH17 : (best_prefix_state_158 rows i best_idx maxu )) (PreH18 : ((Zlength (seen_l)) = 128)) (PreH19 : (reset_prefix_state_158 k seen_l )) ,
  TT && emp 
|--
  “ (seen_l = (zeros (128))) ”
  &&  emp
).

Definition find_max_entail_wit_7_split_goal_1 := 
forall (words_size_pre: Z) (rows: (@list (@list Z))) (seen_l: (@list Z)) (unique: Z) (maxu: Z) (best_idx: Z) (i: Z) (k: Z) (PreH1 : (0 <= (Zlength ((Znth (i) (rows) ((@nil Z))))))) (PreH2 : (k >= 128)) (PreH3 : (0 <= k)) (PreH4 : (k <= 128)) (PreH5 : (0 <= i)) (PreH6 : (i < words_size_pre)) (PreH7 : (0 < words_size_pre)) (PreH8 : (words_size_pre <= 100)) (PreH9 : (0 <= best_idx)) (PreH10 : (best_idx < words_size_pre)) (PreH11 : (0 <= maxu)) (PreH12 : (maxu <= 128)) (PreH13 : (0 <= unique)) (PreH14 : (unique <= 128)) (PreH15 : (rows_well_formed_158 rows words_size_pre )) (PreH16 : (problem_158_pre_z rows )) (PreH17 : (best_prefix_state_158 rows i best_idx maxu )) (PreH18 : ((Zlength (seen_l)) = 128)) (PreH19 : (reset_prefix_state_158 k seen_l )) ,
  TT && emp 
|--
  “ (seen_l = (zeros (128))) ”
.

Definition find_max_entail_wit_8 := 
(
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (i: Z) (best_idx: Z) (maxu: Z) (unique: Z) (PreH1 : (0 <= i)) (PreH2 : (i < words_size_pre)) (PreH3 : (0 < words_size_pre)) (PreH4 : (words_size_pre <= 100)) (PreH5 : (0 <= best_idx)) (PreH6 : (best_idx < words_size_pre)) (PreH7 : (0 <= maxu)) (PreH8 : (maxu <= 128)) (PreH9 : (0 <= unique)) (PreH10 : (unique <= 128)) (PreH11 : (rows_well_formed_158 rows words_size_pre )) (PreH12 : (problem_158_pre_z rows )) (PreH13 : (best_prefix_state_158 rows i best_idx maxu )) ,
  (IntArray.full ( &( "seen" ) ) 128 (zeros (128)) )
  **  (CharPtrArray2.missing_i words_pre words_size_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
|--
  “ (0 <= i) ” 
  &&  “ (i < words_size_pre) ” 
  &&  “ (0 < words_size_pre) ” 
  &&  “ (words_size_pre <= 100) ” 
  &&  “ (0 <= best_idx) ” 
  &&  “ (best_idx < words_size_pre) ” 
  &&  “ (0 <= maxu) ” 
  &&  “ (maxu <= 128) ” 
  &&  “ (0 <= unique) ” 
  &&  “ (unique <= 128) ” 
  &&  “ (rows_well_formed_158 rows words_size_pre ) ” 
  &&  “ (problem_158_pre_z rows ) ” 
  &&  “ (best_prefix_state_158 rows i best_idx maxu ) ” 
  &&  “ (valid_string (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) ) ” 
  &&  “ ((string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX) ” 
  &&  “ ((Zlength ((Znth (i) (rows) ((@nil Z))))) = ((string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) + 1 )) ”
  &&  (CharPtrArray2.missing_i words_pre words_size_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) )
  **  (IntArray.full ( &( "seen" ) ) 128 (zeros (128)) )
) \/
(
forall (words_size_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (i: Z) (best_idx: Z) (maxu: Z) (unique: Z) (PreH1 : (0 <= (Zlength ((Znth (i) (rows) ((@nil Z))))))) (PreH2 : (0 <= i)) (PreH3 : (i < words_size_pre)) (PreH4 : (0 < words_size_pre)) (PreH5 : (words_size_pre <= 100)) (PreH6 : (0 <= best_idx)) (PreH7 : (best_idx < words_size_pre)) (PreH8 : (0 <= maxu)) (PreH9 : (maxu <= 128)) (PreH10 : (0 <= unique)) (PreH11 : (unique <= 128)) (PreH12 : (rows_well_formed_158 rows words_size_pre )) (PreH13 : (problem_158_pre_z rows )) (PreH14 : (best_prefix_state_158 rows i best_idx maxu )) ,
  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
|--
  “ ((Zlength ((Znth (i) (rows) ((@nil Z))))) = ((string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) + 1 )) ” 
  &&  “ ((string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX) ” 
  &&  “ (valid_string (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) ) ”
  &&  (CharArray.full row_ptr ((string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) )
).

Definition find_max_entail_wit_8_split_goal_1 := 
forall (words_size_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (i: Z) (best_idx: Z) (maxu: Z) (unique: Z) (PreH1 : (0 <= (Zlength ((Znth (i) (rows) ((@nil Z))))))) (PreH2 : (0 <= i)) (PreH3 : (i < words_size_pre)) (PreH4 : (0 < words_size_pre)) (PreH5 : (words_size_pre <= 100)) (PreH6 : (0 <= best_idx)) (PreH7 : (best_idx < words_size_pre)) (PreH8 : (0 <= maxu)) (PreH9 : (maxu <= 128)) (PreH10 : (0 <= unique)) (PreH11 : (unique <= 128)) (PreH12 : (rows_well_formed_158 rows words_size_pre )) (PreH13 : (problem_158_pre_z rows )) (PreH14 : (best_prefix_state_158 rows i best_idx maxu )) ,
  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
|--
  “ ((Zlength ((Znth (i) (rows) ((@nil Z))))) = ((string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) + 1 )) ”
.

Definition find_max_entail_wit_8_split_goal_2 := 
forall (words_size_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (i: Z) (best_idx: Z) (maxu: Z) (unique: Z) (PreH1 : (0 <= (Zlength ((Znth (i) (rows) ((@nil Z))))))) (PreH2 : (0 <= i)) (PreH3 : (i < words_size_pre)) (PreH4 : (0 < words_size_pre)) (PreH5 : (words_size_pre <= 100)) (PreH6 : (0 <= best_idx)) (PreH7 : (best_idx < words_size_pre)) (PreH8 : (0 <= maxu)) (PreH9 : (maxu <= 128)) (PreH10 : (0 <= unique)) (PreH11 : (unique <= 128)) (PreH12 : (rows_well_formed_158 rows words_size_pre )) (PreH13 : (problem_158_pre_z rows )) (PreH14 : (best_prefix_state_158 rows i best_idx maxu )) ,
  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
|--
  “ ((string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX) ”
.

Definition find_max_entail_wit_8_split_goal_3 := 
forall (words_size_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (i: Z) (best_idx: Z) (maxu: Z) (unique: Z) (PreH1 : (0 <= (Zlength ((Znth (i) (rows) ((@nil Z))))))) (PreH2 : (0 <= i)) (PreH3 : (i < words_size_pre)) (PreH4 : (0 < words_size_pre)) (PreH5 : (words_size_pre <= 100)) (PreH6 : (0 <= best_idx)) (PreH7 : (best_idx < words_size_pre)) (PreH8 : (0 <= maxu)) (PreH9 : (maxu <= 128)) (PreH10 : (0 <= unique)) (PreH11 : (unique <= 128)) (PreH12 : (rows_well_formed_158 rows words_size_pre )) (PreH13 : (problem_158_pre_z rows )) (PreH14 : (best_prefix_state_158 rows i best_idx maxu )) ,
  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
|--
  “ (valid_string (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) ) ”
.

Definition find_max_entail_wit_8_split_goal_spatial := 
forall (words_size_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (i: Z) (best_idx: Z) (maxu: Z) (unique: Z) (PreH1 : (0 <= (Zlength ((Znth (i) (rows) ((@nil Z))))))) (PreH2 : (0 <= i)) (PreH3 : (i < words_size_pre)) (PreH4 : (0 < words_size_pre)) (PreH5 : (words_size_pre <= 100)) (PreH6 : (0 <= best_idx)) (PreH7 : (best_idx < words_size_pre)) (PreH8 : (0 <= maxu)) (PreH9 : (maxu <= 128)) (PreH10 : (0 <= unique)) (PreH11 : (unique <= 128)) (PreH12 : (rows_well_formed_158 rows words_size_pre )) (PreH13 : (problem_158_pre_z rows )) (PreH14 : (best_prefix_state_158 rows i best_idx maxu )) ,
  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
|--
  (CharArray.full row_ptr ((string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) )
.

Definition find_max_entail_wit_9 := 
(
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (i: Z) (best_idx: Z) (maxu: Z) (unique: Z) (retval: Z) (PreH1 : (retval = (string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))))) (PreH2 : (0 <= ((string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < words_size_pre)) (PreH5 : (0 < words_size_pre)) (PreH6 : (words_size_pre <= 100)) (PreH7 : (0 <= best_idx)) (PreH8 : (best_idx < words_size_pre)) (PreH9 : (0 <= maxu)) (PreH10 : (maxu <= 128)) (PreH11 : (0 <= unique)) (PreH12 : (unique <= 128)) (PreH13 : (rows_well_formed_158 rows words_size_pre )) (PreH14 : (problem_158_pre_z rows )) (PreH15 : (best_prefix_state_158 rows i best_idx maxu )) (PreH16 : (valid_string (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) )) (PreH17 : ((string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX)) (PreH18 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = ((string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) ,
  (store_string row_ptr (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) )
  **  (CharPtrArray2.missing_i words_pre words_size_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full ( &( "seen" ) ) 128 (zeros (128)) )
|--
  EX (seen_l: (@list Z)) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < words_size_pre) ” 
  &&  “ (0 < words_size_pre) ” 
  &&  “ (words_size_pre <= 100) ” 
  &&  “ (0 <= best_idx) ” 
  &&  “ (best_idx < words_size_pre) ” 
  &&  “ (0 <= maxu) ” 
  &&  “ (maxu <= 128) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 128) ” 
  &&  “ (retval = (string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z)))))))) ” 
  &&  “ ((Zlength ((Znth (i) (rows) ((@nil Z))))) = (retval + 1 )) ” 
  &&  “ (valid_string (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 127) ” 
  &&  “ ((Zlength (seen_l)) = 128) ” 
  &&  “ (rows_well_formed_158 rows words_size_pre ) ” 
  &&  “ (problem_158_pre_z rows ) ” 
  &&  “ (best_prefix_state_158 rows i best_idx maxu ) ” 
  &&  “ (count_scan_state_158 (Znth (i) (rows) ((@nil Z))) 0 seen_l 0 ) ”
  &&  (CharPtrArray2.missing_i words_pre words_size_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
  **  (IntArray.full ( &( "seen" ) ) 128 seen_l )
) \/
(
forall (words_size_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (i: Z) (best_idx: Z) (maxu: Z) (unique: Z) (retval: Z) (PreH1 : (retval = (string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))))) (PreH2 : (0 <= ((string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < words_size_pre)) (PreH5 : (0 < words_size_pre)) (PreH6 : (words_size_pre <= 100)) (PreH7 : (0 <= best_idx)) (PreH8 : (best_idx < words_size_pre)) (PreH9 : (0 <= maxu)) (PreH10 : (maxu <= 128)) (PreH11 : (0 <= unique)) (PreH12 : (unique <= 128)) (PreH13 : (rows_well_formed_158 rows words_size_pre )) (PreH14 : (problem_158_pre_z rows )) (PreH15 : (best_prefix_state_158 rows i best_idx maxu )) (PreH16 : (valid_string (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) )) (PreH17 : ((string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX)) (PreH18 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = ((string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) ,
  (CharArray.full row_ptr ((string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) )
|--
  “ (count_scan_state_158 (Znth (i) (rows) ((@nil Z))) 0 (zeros (128)) 0 ) ” 
  &&  “ ((Zlength ((zeros (128)))) = 128) ” 
  &&  “ ((Zlength ((Znth (i) (rows) ((@nil Z))))) = (retval + 1 )) ” 
  &&  “ (0 <= retval) ”
  &&  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
).

Definition find_max_entail_wit_9_split_goal_1 := 
forall (words_size_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (i: Z) (best_idx: Z) (maxu: Z) (unique: Z) (retval: Z) (PreH1 : (retval = (string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))))) (PreH2 : (0 <= ((string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < words_size_pre)) (PreH5 : (0 < words_size_pre)) (PreH6 : (words_size_pre <= 100)) (PreH7 : (0 <= best_idx)) (PreH8 : (best_idx < words_size_pre)) (PreH9 : (0 <= maxu)) (PreH10 : (maxu <= 128)) (PreH11 : (0 <= unique)) (PreH12 : (unique <= 128)) (PreH13 : (rows_well_formed_158 rows words_size_pre )) (PreH14 : (problem_158_pre_z rows )) (PreH15 : (best_prefix_state_158 rows i best_idx maxu )) (PreH16 : (valid_string (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) )) (PreH17 : ((string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX)) (PreH18 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = ((string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) ,
  (CharArray.full row_ptr ((string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) )
|--
  “ (count_scan_state_158 (Znth (i) (rows) ((@nil Z))) 0 (zeros (128)) 0 ) ”
.

Definition find_max_entail_wit_9_split_goal_2 := 
forall (words_size_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (i: Z) (best_idx: Z) (maxu: Z) (unique: Z) (retval: Z) (PreH1 : (retval = (string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))))) (PreH2 : (0 <= ((string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < words_size_pre)) (PreH5 : (0 < words_size_pre)) (PreH6 : (words_size_pre <= 100)) (PreH7 : (0 <= best_idx)) (PreH8 : (best_idx < words_size_pre)) (PreH9 : (0 <= maxu)) (PreH10 : (maxu <= 128)) (PreH11 : (0 <= unique)) (PreH12 : (unique <= 128)) (PreH13 : (rows_well_formed_158 rows words_size_pre )) (PreH14 : (problem_158_pre_z rows )) (PreH15 : (best_prefix_state_158 rows i best_idx maxu )) (PreH16 : (valid_string (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) )) (PreH17 : ((string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX)) (PreH18 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = ((string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) ,
  (CharArray.full row_ptr ((string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) )
|--
  “ ((Zlength ((zeros (128)))) = 128) ”
.

Definition find_max_entail_wit_9_split_goal_3 := 
forall (words_size_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (i: Z) (best_idx: Z) (maxu: Z) (unique: Z) (retval: Z) (PreH1 : (retval = (string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))))) (PreH2 : (0 <= ((string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < words_size_pre)) (PreH5 : (0 < words_size_pre)) (PreH6 : (words_size_pre <= 100)) (PreH7 : (0 <= best_idx)) (PreH8 : (best_idx < words_size_pre)) (PreH9 : (0 <= maxu)) (PreH10 : (maxu <= 128)) (PreH11 : (0 <= unique)) (PreH12 : (unique <= 128)) (PreH13 : (rows_well_formed_158 rows words_size_pre )) (PreH14 : (problem_158_pre_z rows )) (PreH15 : (best_prefix_state_158 rows i best_idx maxu )) (PreH16 : (valid_string (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) )) (PreH17 : ((string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX)) (PreH18 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = ((string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) ,
  (CharArray.full row_ptr ((string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) )
|--
  “ ((Zlength ((Znth (i) (rows) ((@nil Z))))) = (retval + 1 )) ”
.

Definition find_max_entail_wit_9_split_goal_4 := 
forall (words_size_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (i: Z) (best_idx: Z) (maxu: Z) (unique: Z) (retval: Z) (PreH1 : (retval = (string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))))) (PreH2 : (0 <= ((string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < words_size_pre)) (PreH5 : (0 < words_size_pre)) (PreH6 : (words_size_pre <= 100)) (PreH7 : (0 <= best_idx)) (PreH8 : (best_idx < words_size_pre)) (PreH9 : (0 <= maxu)) (PreH10 : (maxu <= 128)) (PreH11 : (0 <= unique)) (PreH12 : (unique <= 128)) (PreH13 : (rows_well_formed_158 rows words_size_pre )) (PreH14 : (problem_158_pre_z rows )) (PreH15 : (best_prefix_state_158 rows i best_idx maxu )) (PreH16 : (valid_string (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) )) (PreH17 : ((string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX)) (PreH18 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = ((string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) ,
  (CharArray.full row_ptr ((string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) )
|--
  “ (0 <= retval) ”
.

Definition find_max_entail_wit_9_split_goal_spatial := 
forall (words_size_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (i: Z) (best_idx: Z) (maxu: Z) (unique: Z) (retval: Z) (PreH1 : (retval = (string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))))) (PreH2 : (0 <= ((string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < words_size_pre)) (PreH5 : (0 < words_size_pre)) (PreH6 : (words_size_pre <= 100)) (PreH7 : (0 <= best_idx)) (PreH8 : (best_idx < words_size_pre)) (PreH9 : (0 <= maxu)) (PreH10 : (maxu <= 128)) (PreH11 : (0 <= unique)) (PreH12 : (unique <= 128)) (PreH13 : (rows_well_formed_158 rows words_size_pre )) (PreH14 : (problem_158_pre_z rows )) (PreH15 : (best_prefix_state_158 rows i best_idx maxu )) (PreH16 : (valid_string (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) )) (PreH17 : ((string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX)) (PreH18 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = ((string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) ,
  (CharArray.full row_ptr ((string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) )
|--
  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
.

Definition find_max_entail_wit_10 := 
(
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (seen_l_2: (@list Z)) (ch: Z) (unique: Z) (maxu: Z) (best_idx: Z) (row_ptr: Z) (i: Z) (len: Z) (j: Z) (PreH1 : (j < len)) (PreH2 : (0 <= j)) (PreH3 : (j <= len)) (PreH4 : (0 <= i)) (PreH5 : (i < words_size_pre)) (PreH6 : (0 < words_size_pre)) (PreH7 : (words_size_pre <= 100)) (PreH8 : (0 <= best_idx)) (PreH9 : (best_idx < words_size_pre)) (PreH10 : (0 <= maxu)) (PreH11 : (maxu <= 128)) (PreH12 : (0 <= unique)) (PreH13 : (unique <= 128)) (PreH14 : (len = (string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))))) (PreH15 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = (len + 1 ))) (PreH16 : (valid_string (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) )) (PreH17 : (0 <= ch)) (PreH18 : (ch <= 127)) (PreH19 : ((Zlength (seen_l_2)) = 128)) (PreH20 : (rows_well_formed_158 rows words_size_pre )) (PreH21 : (problem_158_pre_z rows )) (PreH22 : (best_prefix_state_158 rows i best_idx maxu )) (PreH23 : (count_scan_state_158 (Znth (i) (rows) ((@nil Z))) j seen_l_2 unique )) ,
  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
  **  (CharPtrArray2.missing_i words_pre words_size_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full ( &( "seen" ) ) 128 seen_l_2 )
|--
  EX (seen_l: (@list Z)) ,
  “ (0 <= j) ” 
  &&  “ (j < len) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < words_size_pre) ” 
  &&  “ (0 < words_size_pre) ” 
  &&  “ (words_size_pre <= 100) ” 
  &&  “ (0 <= (Znth j (Znth (i) (rows) ((@nil Z))) 0)) ” 
  &&  “ ((Znth j (Znth (i) (rows) ((@nil Z))) 0) < 128) ” 
  &&  “ ((Znth j (Znth (i) (rows) ((@nil Z))) 0) = (Znth (j) ((Znth (i) (rows) ((@nil Z)))) (0))) ” 
  &&  “ (0 <= best_idx) ” 
  &&  “ (best_idx < words_size_pre) ” 
  &&  “ (0 <= maxu) ” 
  &&  “ (maxu <= 128) ” 
  &&  “ (0 <= unique) ” 
  &&  “ (unique <= 128) ” 
  &&  “ (len = (string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z)))))))) ” 
  &&  “ ((Zlength ((Znth (i) (rows) ((@nil Z))))) = (len + 1 )) ” 
  &&  “ (valid_string (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) ) ” 
  &&  “ ((Zlength (seen_l)) = 128) ” 
  &&  “ (rows_well_formed_158 rows words_size_pre ) ” 
  &&  “ (problem_158_pre_z rows ) ” 
  &&  “ (best_prefix_state_158 rows i best_idx maxu ) ” 
  &&  “ (count_scan_state_158 (Znth (i) (rows) ((@nil Z))) j seen_l unique ) ”
  &&  (CharPtrArray2.missing_i words_pre words_size_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
  **  (IntArray.full ( &( "seen" ) ) 128 seen_l )
) \/
(
forall (words_size_pre: Z) (rows: (@list (@list Z))) (seen_l_2: (@list Z)) (ch: Z) (unique: Z) (maxu: Z) (best_idx: Z) (i: Z) (len: Z) (j: Z) (PreH1 : (j < len)) (PreH2 : (0 <= j)) (PreH3 : (j <= len)) (PreH4 : (0 <= i)) (PreH5 : (i < words_size_pre)) (PreH6 : (0 < words_size_pre)) (PreH7 : (words_size_pre <= 100)) (PreH8 : (0 <= best_idx)) (PreH9 : (best_idx < words_size_pre)) (PreH10 : (0 <= maxu)) (PreH11 : (maxu <= 128)) (PreH12 : (0 <= unique)) (PreH13 : (unique <= 128)) (PreH14 : (len = (string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))))) (PreH15 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = (len + 1 ))) (PreH16 : (valid_string (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) )) (PreH17 : (0 <= ch)) (PreH18 : (ch <= 127)) (PreH19 : ((Zlength (seen_l_2)) = 128)) (PreH20 : (rows_well_formed_158 rows words_size_pre )) (PreH21 : (problem_158_pre_z rows )) (PreH22 : (best_prefix_state_158 rows i best_idx maxu )) (PreH23 : (count_scan_state_158 (Znth (i) (rows) ((@nil Z))) j seen_l_2 unique )) ,
  TT && emp 
|--
  “ ((Znth j (Znth (i) (rows) ((@nil Z))) 0) = (Znth (j) ((Znth (i) (rows) ((@nil Z)))) (0))) ” 
  &&  “ ((Znth j (Znth (i) (rows) ((@nil Z))) 0) < 128) ” 
  &&  “ (0 <= (Znth j (Znth (i) (rows) ((@nil Z))) 0)) ”
  &&  emp
).

Definition find_max_entail_wit_10_split_goal_1 := 
forall (words_size_pre: Z) (rows: (@list (@list Z))) (seen_l_2: (@list Z)) (ch: Z) (unique: Z) (maxu: Z) (best_idx: Z) (i: Z) (len: Z) (j: Z) (PreH1 : (j < len)) (PreH2 : (0 <= j)) (PreH3 : (j <= len)) (PreH4 : (0 <= i)) (PreH5 : (i < words_size_pre)) (PreH6 : (0 < words_size_pre)) (PreH7 : (words_size_pre <= 100)) (PreH8 : (0 <= best_idx)) (PreH9 : (best_idx < words_size_pre)) (PreH10 : (0 <= maxu)) (PreH11 : (maxu <= 128)) (PreH12 : (0 <= unique)) (PreH13 : (unique <= 128)) (PreH14 : (len = (string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))))) (PreH15 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = (len + 1 ))) (PreH16 : (valid_string (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) )) (PreH17 : (0 <= ch)) (PreH18 : (ch <= 127)) (PreH19 : ((Zlength (seen_l_2)) = 128)) (PreH20 : (rows_well_formed_158 rows words_size_pre )) (PreH21 : (problem_158_pre_z rows )) (PreH22 : (best_prefix_state_158 rows i best_idx maxu )) (PreH23 : (count_scan_state_158 (Znth (i) (rows) ((@nil Z))) j seen_l_2 unique )) ,
  TT && emp 
|--
  “ ((Znth j (Znth (i) (rows) ((@nil Z))) 0) = (Znth (j) ((Znth (i) (rows) ((@nil Z)))) (0))) ”
.

Definition find_max_entail_wit_10_split_goal_2 := 
forall (words_size_pre: Z) (rows: (@list (@list Z))) (seen_l_2: (@list Z)) (ch: Z) (unique: Z) (maxu: Z) (best_idx: Z) (i: Z) (len: Z) (j: Z) (PreH1 : (j < len)) (PreH2 : (0 <= j)) (PreH3 : (j <= len)) (PreH4 : (0 <= i)) (PreH5 : (i < words_size_pre)) (PreH6 : (0 < words_size_pre)) (PreH7 : (words_size_pre <= 100)) (PreH8 : (0 <= best_idx)) (PreH9 : (best_idx < words_size_pre)) (PreH10 : (0 <= maxu)) (PreH11 : (maxu <= 128)) (PreH12 : (0 <= unique)) (PreH13 : (unique <= 128)) (PreH14 : (len = (string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))))) (PreH15 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = (len + 1 ))) (PreH16 : (valid_string (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) )) (PreH17 : (0 <= ch)) (PreH18 : (ch <= 127)) (PreH19 : ((Zlength (seen_l_2)) = 128)) (PreH20 : (rows_well_formed_158 rows words_size_pre )) (PreH21 : (problem_158_pre_z rows )) (PreH22 : (best_prefix_state_158 rows i best_idx maxu )) (PreH23 : (count_scan_state_158 (Znth (i) (rows) ((@nil Z))) j seen_l_2 unique )) ,
  TT && emp 
|--
  “ ((Znth j (Znth (i) (rows) ((@nil Z))) 0) < 128) ”
.

Definition find_max_entail_wit_10_split_goal_3 := 
forall (words_size_pre: Z) (rows: (@list (@list Z))) (seen_l_2: (@list Z)) (ch: Z) (unique: Z) (maxu: Z) (best_idx: Z) (i: Z) (len: Z) (j: Z) (PreH1 : (j < len)) (PreH2 : (0 <= j)) (PreH3 : (j <= len)) (PreH4 : (0 <= i)) (PreH5 : (i < words_size_pre)) (PreH6 : (0 < words_size_pre)) (PreH7 : (words_size_pre <= 100)) (PreH8 : (0 <= best_idx)) (PreH9 : (best_idx < words_size_pre)) (PreH10 : (0 <= maxu)) (PreH11 : (maxu <= 128)) (PreH12 : (0 <= unique)) (PreH13 : (unique <= 128)) (PreH14 : (len = (string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))))) (PreH15 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = (len + 1 ))) (PreH16 : (valid_string (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) )) (PreH17 : (0 <= ch)) (PreH18 : (ch <= 127)) (PreH19 : ((Zlength (seen_l_2)) = 128)) (PreH20 : (rows_well_formed_158 rows words_size_pre )) (PreH21 : (problem_158_pre_z rows )) (PreH22 : (best_prefix_state_158 rows i best_idx maxu )) (PreH23 : (count_scan_state_158 (Znth (i) (rows) ((@nil Z))) j seen_l_2 unique )) ,
  TT && emp 
|--
  “ (0 <= (Znth j (Znth (i) (rows) ((@nil Z))) 0)) ”
.

Definition find_max_entail_wit_11_1 := 
(
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (seen_l_2: (@list Z)) (j: Z) (len: Z) (i: Z) (ch: Z) (best_idx: Z) (maxu: Z) (unique: Z) (PreH1 : ((Znth ch seen_l_2 0) = 0)) (PreH2 : (0 <= (Zlength ((Znth (i) (rows) ((@nil Z))))))) (PreH3 : (0 <= j)) (PreH4 : (j < len)) (PreH5 : (0 <= i)) (PreH6 : (i < words_size_pre)) (PreH7 : (0 < words_size_pre)) (PreH8 : (words_size_pre <= 100)) (PreH9 : (0 <= ch)) (PreH10 : (ch < 128)) (PreH11 : (ch = (Znth (j) ((Znth (i) (rows) ((@nil Z)))) (0)))) (PreH12 : (0 <= best_idx)) (PreH13 : (best_idx < words_size_pre)) (PreH14 : (0 <= maxu)) (PreH15 : (maxu <= 128)) (PreH16 : (0 <= unique)) (PreH17 : (unique <= 128)) (PreH18 : (len = (string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))))) (PreH19 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = (len + 1 ))) (PreH20 : (valid_string (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) )) (PreH21 : ((Zlength (seen_l_2)) = 128)) (PreH22 : (rows_well_formed_158 rows words_size_pre )) (PreH23 : (problem_158_pre_z rows )) (PreH24 : (best_prefix_state_158 rows i best_idx maxu )) (PreH25 : (count_scan_state_158 (Znth (i) (rows) ((@nil Z))) j seen_l_2 unique )) ,
  (IntArray.full ( &( "seen" ) ) 128 (replace_Znth (ch) (1) (seen_l_2)) )
  **  (CharPtrArray2.missing_i words_pre words_size_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
|--
  EX (seen_l: (@list Z)) ,
  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= len) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < words_size_pre) ” 
  &&  “ (0 < words_size_pre) ” 
  &&  “ (words_size_pre <= 100) ” 
  &&  “ (0 <= best_idx) ” 
  &&  “ (best_idx < words_size_pre) ” 
  &&  “ (0 <= maxu) ” 
  &&  “ (maxu <= 128) ” 
  &&  “ (0 <= (unique + 1 )) ” 
  &&  “ ((unique + 1 ) <= 128) ” 
  &&  “ (len = (string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z)))))))) ” 
  &&  “ ((Zlength ((Znth (i) (rows) ((@nil Z))))) = (len + 1 )) ” 
  &&  “ (valid_string (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) ) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ ((Zlength (seen_l)) = 128) ” 
  &&  “ (rows_well_formed_158 rows words_size_pre ) ” 
  &&  “ (problem_158_pre_z rows ) ” 
  &&  “ (best_prefix_state_158 rows i best_idx maxu ) ” 
  &&  “ (count_scan_state_158 (Znth (i) (rows) ((@nil Z))) (j + 1 ) seen_l (unique + 1 ) ) ”
  &&  (CharPtrArray2.missing_i words_pre words_size_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
  **  (IntArray.full ( &( "seen" ) ) 128 seen_l )
) \/
(
forall (words_size_pre: Z) (rows: (@list (@list Z))) (seen_l_2: (@list Z)) (j: Z) (len: Z) (i: Z) (ch: Z) (best_idx: Z) (maxu: Z) (unique: Z) (PreH1 : ((Znth ch seen_l_2 0) = 0)) (PreH2 : (0 <= (Zlength ((Znth (i) (rows) ((@nil Z))))))) (PreH3 : (0 <= j)) (PreH4 : (j < len)) (PreH5 : (0 <= i)) (PreH6 : (i < words_size_pre)) (PreH7 : (0 < words_size_pre)) (PreH8 : (words_size_pre <= 100)) (PreH9 : (0 <= ch)) (PreH10 : (ch < 128)) (PreH11 : (ch = (Znth (j) ((Znth (i) (rows) ((@nil Z)))) (0)))) (PreH12 : (0 <= best_idx)) (PreH13 : (best_idx < words_size_pre)) (PreH14 : (0 <= maxu)) (PreH15 : (maxu <= 128)) (PreH16 : (0 <= unique)) (PreH17 : (unique <= 128)) (PreH18 : (len = (string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))))) (PreH19 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = (len + 1 ))) (PreH20 : (valid_string (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) )) (PreH21 : ((Zlength (seen_l_2)) = 128)) (PreH22 : (rows_well_formed_158 rows words_size_pre )) (PreH23 : (problem_158_pre_z rows )) (PreH24 : (best_prefix_state_158 rows i best_idx maxu )) (PreH25 : (count_scan_state_158 (Znth (i) (rows) ((@nil Z))) j seen_l_2 unique )) ,
  TT && emp 
|--
  “ (count_scan_state_158 (Znth (i) (rows) ((@nil Z))) (j + 1 ) (replace_Znth (ch) (1) (seen_l_2)) (unique + 1 ) ) ” 
  &&  “ ((Zlength ((replace_Znth (ch) (1) (seen_l_2)))) = 128) ” 
  &&  “ ((unique + 1 ) <= 128) ”
  &&  emp
).

Definition find_max_entail_wit_11_1_split_goal_1 := 
forall (words_size_pre: Z) (rows: (@list (@list Z))) (seen_l_2: (@list Z)) (j: Z) (len: Z) (i: Z) (ch: Z) (best_idx: Z) (maxu: Z) (unique: Z) (PreH1 : ((Znth ch seen_l_2 0) = 0)) (PreH2 : (0 <= (Zlength ((Znth (i) (rows) ((@nil Z))))))) (PreH3 : (0 <= j)) (PreH4 : (j < len)) (PreH5 : (0 <= i)) (PreH6 : (i < words_size_pre)) (PreH7 : (0 < words_size_pre)) (PreH8 : (words_size_pre <= 100)) (PreH9 : (0 <= ch)) (PreH10 : (ch < 128)) (PreH11 : (ch = (Znth (j) ((Znth (i) (rows) ((@nil Z)))) (0)))) (PreH12 : (0 <= best_idx)) (PreH13 : (best_idx < words_size_pre)) (PreH14 : (0 <= maxu)) (PreH15 : (maxu <= 128)) (PreH16 : (0 <= unique)) (PreH17 : (unique <= 128)) (PreH18 : (len = (string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))))) (PreH19 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = (len + 1 ))) (PreH20 : (valid_string (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) )) (PreH21 : ((Zlength (seen_l_2)) = 128)) (PreH22 : (rows_well_formed_158 rows words_size_pre )) (PreH23 : (problem_158_pre_z rows )) (PreH24 : (best_prefix_state_158 rows i best_idx maxu )) (PreH25 : (count_scan_state_158 (Znth (i) (rows) ((@nil Z))) j seen_l_2 unique )) ,
  TT && emp 
|--
  “ (count_scan_state_158 (Znth (i) (rows) ((@nil Z))) (j + 1 ) (replace_Znth (ch) (1) (seen_l_2)) (unique + 1 ) ) ”
.

Definition find_max_entail_wit_11_1_split_goal_2 := 
forall (words_size_pre: Z) (rows: (@list (@list Z))) (seen_l_2: (@list Z)) (j: Z) (len: Z) (i: Z) (ch: Z) (best_idx: Z) (maxu: Z) (unique: Z) (PreH1 : ((Znth ch seen_l_2 0) = 0)) (PreH2 : (0 <= (Zlength ((Znth (i) (rows) ((@nil Z))))))) (PreH3 : (0 <= j)) (PreH4 : (j < len)) (PreH5 : (0 <= i)) (PreH6 : (i < words_size_pre)) (PreH7 : (0 < words_size_pre)) (PreH8 : (words_size_pre <= 100)) (PreH9 : (0 <= ch)) (PreH10 : (ch < 128)) (PreH11 : (ch = (Znth (j) ((Znth (i) (rows) ((@nil Z)))) (0)))) (PreH12 : (0 <= best_idx)) (PreH13 : (best_idx < words_size_pre)) (PreH14 : (0 <= maxu)) (PreH15 : (maxu <= 128)) (PreH16 : (0 <= unique)) (PreH17 : (unique <= 128)) (PreH18 : (len = (string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))))) (PreH19 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = (len + 1 ))) (PreH20 : (valid_string (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) )) (PreH21 : ((Zlength (seen_l_2)) = 128)) (PreH22 : (rows_well_formed_158 rows words_size_pre )) (PreH23 : (problem_158_pre_z rows )) (PreH24 : (best_prefix_state_158 rows i best_idx maxu )) (PreH25 : (count_scan_state_158 (Znth (i) (rows) ((@nil Z))) j seen_l_2 unique )) ,
  TT && emp 
|--
  “ ((Zlength ((replace_Znth (ch) (1) (seen_l_2)))) = 128) ”
.

Definition find_max_entail_wit_11_1_split_goal_3 := 
forall (words_size_pre: Z) (rows: (@list (@list Z))) (seen_l_2: (@list Z)) (j: Z) (len: Z) (i: Z) (ch: Z) (best_idx: Z) (maxu: Z) (unique: Z) (PreH1 : ((Znth ch seen_l_2 0) = 0)) (PreH2 : (0 <= (Zlength ((Znth (i) (rows) ((@nil Z))))))) (PreH3 : (0 <= j)) (PreH4 : (j < len)) (PreH5 : (0 <= i)) (PreH6 : (i < words_size_pre)) (PreH7 : (0 < words_size_pre)) (PreH8 : (words_size_pre <= 100)) (PreH9 : (0 <= ch)) (PreH10 : (ch < 128)) (PreH11 : (ch = (Znth (j) ((Znth (i) (rows) ((@nil Z)))) (0)))) (PreH12 : (0 <= best_idx)) (PreH13 : (best_idx < words_size_pre)) (PreH14 : (0 <= maxu)) (PreH15 : (maxu <= 128)) (PreH16 : (0 <= unique)) (PreH17 : (unique <= 128)) (PreH18 : (len = (string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))))) (PreH19 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = (len + 1 ))) (PreH20 : (valid_string (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) )) (PreH21 : ((Zlength (seen_l_2)) = 128)) (PreH22 : (rows_well_formed_158 rows words_size_pre )) (PreH23 : (problem_158_pre_z rows )) (PreH24 : (best_prefix_state_158 rows i best_idx maxu )) (PreH25 : (count_scan_state_158 (Znth (i) (rows) ((@nil Z))) j seen_l_2 unique )) ,
  TT && emp 
|--
  “ ((unique + 1 ) <= 128) ”
.

Definition find_max_entail_wit_11_2 := 
(
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (seen_l_2: (@list Z)) (j: Z) (len: Z) (i: Z) (ch: Z) (best_idx: Z) (maxu: Z) (unique: Z) (PreH1 : ((Znth ch seen_l_2 0) <> 0)) (PreH2 : (0 <= (Zlength ((Znth (i) (rows) ((@nil Z))))))) (PreH3 : (0 <= j)) (PreH4 : (j < len)) (PreH5 : (0 <= i)) (PreH6 : (i < words_size_pre)) (PreH7 : (0 < words_size_pre)) (PreH8 : (words_size_pre <= 100)) (PreH9 : (0 <= ch)) (PreH10 : (ch < 128)) (PreH11 : (ch = (Znth (j) ((Znth (i) (rows) ((@nil Z)))) (0)))) (PreH12 : (0 <= best_idx)) (PreH13 : (best_idx < words_size_pre)) (PreH14 : (0 <= maxu)) (PreH15 : (maxu <= 128)) (PreH16 : (0 <= unique)) (PreH17 : (unique <= 128)) (PreH18 : (len = (string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))))) (PreH19 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = (len + 1 ))) (PreH20 : (valid_string (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) )) (PreH21 : ((Zlength (seen_l_2)) = 128)) (PreH22 : (rows_well_formed_158 rows words_size_pre )) (PreH23 : (problem_158_pre_z rows )) (PreH24 : (best_prefix_state_158 rows i best_idx maxu )) (PreH25 : (count_scan_state_158 (Znth (i) (rows) ((@nil Z))) j seen_l_2 unique )) ,
  (IntArray.full ( &( "seen" ) ) 128 seen_l_2 )
  **  (CharPtrArray2.missing_i words_pre words_size_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
|--
  EX (seen_l: (@list Z)) ,
  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= len) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < words_size_pre) ” 
  &&  “ (0 < words_size_pre) ” 
  &&  “ (words_size_pre <= 100) ” 
  &&  “ (0 <= best_idx) ” 
  &&  “ (best_idx < words_size_pre) ” 
  &&  “ (0 <= maxu) ” 
  &&  “ (maxu <= 128) ” 
  &&  “ (0 <= unique) ” 
  &&  “ (unique <= 128) ” 
  &&  “ (len = (string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z)))))))) ” 
  &&  “ ((Zlength ((Znth (i) (rows) ((@nil Z))))) = (len + 1 )) ” 
  &&  “ (valid_string (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) ) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ ((Zlength (seen_l)) = 128) ” 
  &&  “ (rows_well_formed_158 rows words_size_pre ) ” 
  &&  “ (problem_158_pre_z rows ) ” 
  &&  “ (best_prefix_state_158 rows i best_idx maxu ) ” 
  &&  “ (count_scan_state_158 (Znth (i) (rows) ((@nil Z))) (j + 1 ) seen_l unique ) ”
  &&  (CharPtrArray2.missing_i words_pre words_size_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
  **  (IntArray.full ( &( "seen" ) ) 128 seen_l )
) \/
(
forall (words_size_pre: Z) (rows: (@list (@list Z))) (seen_l_2: (@list Z)) (j: Z) (len: Z) (i: Z) (ch: Z) (best_idx: Z) (maxu: Z) (unique: Z) (PreH1 : ((Znth ch seen_l_2 0) <> 0)) (PreH2 : (0 <= (Zlength ((Znth (i) (rows) ((@nil Z))))))) (PreH3 : (0 <= j)) (PreH4 : (j < len)) (PreH5 : (0 <= i)) (PreH6 : (i < words_size_pre)) (PreH7 : (0 < words_size_pre)) (PreH8 : (words_size_pre <= 100)) (PreH9 : (0 <= ch)) (PreH10 : (ch < 128)) (PreH11 : (ch = (Znth (j) ((Znth (i) (rows) ((@nil Z)))) (0)))) (PreH12 : (0 <= best_idx)) (PreH13 : (best_idx < words_size_pre)) (PreH14 : (0 <= maxu)) (PreH15 : (maxu <= 128)) (PreH16 : (0 <= unique)) (PreH17 : (unique <= 128)) (PreH18 : (len = (string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))))) (PreH19 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = (len + 1 ))) (PreH20 : (valid_string (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) )) (PreH21 : ((Zlength (seen_l_2)) = 128)) (PreH22 : (rows_well_formed_158 rows words_size_pre )) (PreH23 : (problem_158_pre_z rows )) (PreH24 : (best_prefix_state_158 rows i best_idx maxu )) (PreH25 : (count_scan_state_158 (Znth (i) (rows) ((@nil Z))) j seen_l_2 unique )) ,
  TT && emp 
|--
  “ (count_scan_state_158 (Znth (i) (rows) ((@nil Z))) (j + 1 ) seen_l_2 unique ) ”
  &&  emp
).

Definition find_max_entail_wit_11_2_split_goal_1 := 
forall (words_size_pre: Z) (rows: (@list (@list Z))) (seen_l_2: (@list Z)) (j: Z) (len: Z) (i: Z) (ch: Z) (best_idx: Z) (maxu: Z) (unique: Z) (PreH1 : ((Znth ch seen_l_2 0) <> 0)) (PreH2 : (0 <= (Zlength ((Znth (i) (rows) ((@nil Z))))))) (PreH3 : (0 <= j)) (PreH4 : (j < len)) (PreH5 : (0 <= i)) (PreH6 : (i < words_size_pre)) (PreH7 : (0 < words_size_pre)) (PreH8 : (words_size_pre <= 100)) (PreH9 : (0 <= ch)) (PreH10 : (ch < 128)) (PreH11 : (ch = (Znth (j) ((Znth (i) (rows) ((@nil Z)))) (0)))) (PreH12 : (0 <= best_idx)) (PreH13 : (best_idx < words_size_pre)) (PreH14 : (0 <= maxu)) (PreH15 : (maxu <= 128)) (PreH16 : (0 <= unique)) (PreH17 : (unique <= 128)) (PreH18 : (len = (string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))))) (PreH19 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = (len + 1 ))) (PreH20 : (valid_string (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) )) (PreH21 : ((Zlength (seen_l_2)) = 128)) (PreH22 : (rows_well_formed_158 rows words_size_pre )) (PreH23 : (problem_158_pre_z rows )) (PreH24 : (best_prefix_state_158 rows i best_idx maxu )) (PreH25 : (count_scan_state_158 (Znth (i) (rows) ((@nil Z))) j seen_l_2 unique )) ,
  TT && emp 
|--
  “ (count_scan_state_158 (Znth (i) (rows) ((@nil Z))) (j + 1 ) seen_l_2 unique ) ”
.

Definition find_max_entail_wit_12 := 
(
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (seen_l_2: (@list Z)) (ch: Z) (unique: Z) (maxu: Z) (best_idx: Z) (row_ptr: Z) (i: Z) (len: Z) (j: Z) (PreH1 : (i <> best_idx)) (PreH2 : (unique = maxu)) (PreH3 : (unique <= maxu)) (PreH4 : (j >= len)) (PreH5 : (0 <= j)) (PreH6 : (j <= len)) (PreH7 : (0 <= i)) (PreH8 : (i < words_size_pre)) (PreH9 : (0 < words_size_pre)) (PreH10 : (words_size_pre <= 100)) (PreH11 : (0 <= best_idx)) (PreH12 : (best_idx < words_size_pre)) (PreH13 : (0 <= maxu)) (PreH14 : (maxu <= 128)) (PreH15 : (0 <= unique)) (PreH16 : (unique <= 128)) (PreH17 : (len = (string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))))) (PreH18 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = (len + 1 ))) (PreH19 : (valid_string (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) )) (PreH20 : (0 <= ch)) (PreH21 : (ch <= 127)) (PreH22 : ((Zlength (seen_l_2)) = 128)) (PreH23 : (rows_well_formed_158 rows words_size_pre )) (PreH24 : (problem_158_pre_z rows )) (PreH25 : (best_prefix_state_158 rows i best_idx maxu )) (PreH26 : (count_scan_state_158 (Znth (i) (rows) ((@nil Z))) j seen_l_2 unique )) ,
  (CharPtrArray2.missing_i words_pre words_size_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
  **  (IntArray.full ( &( "seen" ) ) 128 seen_l_2 )
|--
  EX (best_ptr: Z)  (seen_l: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i < words_size_pre) ” 
  &&  “ (0 < words_size_pre) ” 
  &&  “ (words_size_pre <= 100) ” 
  &&  “ (0 <= best_idx) ” 
  &&  “ (best_idx < words_size_pre) ” 
  &&  “ (i <> best_idx) ” 
  &&  “ (unique = (row_unique_count_z_158 ((Znth (i) (rows) ((@nil Z)))))) ” 
  &&  “ (unique = maxu) ” 
  &&  “ (0 <= maxu) ” 
  &&  “ (maxu <= 128) ” 
  &&  “ (0 <= unique) ” 
  &&  “ (unique <= 128) ” 
  &&  “ (rows_well_formed_158 rows words_size_pre ) ” 
  &&  “ (problem_158_pre_z rows ) ” 
  &&  “ (best_prefix_state_158 rows i best_idx maxu ) ” 
  &&  “ (valid_string (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) ) ” 
  &&  “ (valid_string (row_payload_z_158 ((Znth (best_idx) (rows) ((@nil Z))))) ) ” 
  &&  “ ((string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX) ” 
  &&  “ ((string_length ((row_payload_z_158 ((Znth (best_idx) (rows) ((@nil Z))))))) < INT_MAX) ” 
  &&  “ ((Zlength (seen_l)) = 128) ”
  &&  (char_ptr_array2_missing_two_158 words_pre words_size_pre i row_ptr best_idx best_ptr rows )
  **  (store_string row_ptr (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) )
  **  (((words_pre + (best_idx * sizeof(PTR) ) )) # Ptr  |-> best_ptr)
  **  (store_string best_ptr (row_payload_z_158 ((Znth (best_idx) (rows) ((@nil Z))))) )
  **  (IntArray.full ( &( "seen" ) ) 128 seen_l )
) \/
(
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (seen_l_2: (@list Z)) (ch: Z) (unique: Z) (maxu: Z) (best_idx: Z) (row_ptr: Z) (i: Z) (len: Z) (j: Z) (PreH1 : (0 <= (Zlength ((Znth (i) (rows) ((@nil Z))))))) (PreH2 : (i <> best_idx)) (PreH3 : (unique = maxu)) (PreH4 : (unique <= maxu)) (PreH5 : (j >= len)) (PreH6 : (0 <= j)) (PreH7 : (j <= len)) (PreH8 : (0 <= i)) (PreH9 : (i < words_size_pre)) (PreH10 : (0 < words_size_pre)) (PreH11 : (words_size_pre <= 100)) (PreH12 : (0 <= best_idx)) (PreH13 : (best_idx < words_size_pre)) (PreH14 : (0 <= maxu)) (PreH15 : (maxu <= 128)) (PreH16 : (0 <= unique)) (PreH17 : (unique <= 128)) (PreH18 : (len = (string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))))) (PreH19 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = (len + 1 ))) (PreH20 : (valid_string (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) )) (PreH21 : (0 <= ch)) (PreH22 : (ch <= 127)) (PreH23 : ((Zlength (seen_l_2)) = 128)) (PreH24 : (rows_well_formed_158 rows words_size_pre )) (PreH25 : (problem_158_pre_z rows )) (PreH26 : (best_prefix_state_158 rows i best_idx maxu )) (PreH27 : (count_scan_state_158 (Znth (i) (rows) ((@nil Z))) j seen_l_2 unique )) ,
  (CharPtrArray2.missing_i words_pre words_size_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
|--
  EX (best_ptr: Z) ,
  “ (0 <= i) ” 
  &&  “ (i < words_size_pre) ” 
  &&  “ (0 < words_size_pre) ” 
  &&  “ (words_size_pre <= 100) ” 
  &&  “ (0 <= best_idx) ” 
  &&  “ (best_idx < words_size_pre) ” 
  &&  “ (i <> best_idx) ” 
  &&  “ (unique = (row_unique_count_z_158 ((Znth (i) (rows) ((@nil Z)))))) ” 
  &&  “ (unique = maxu) ” 
  &&  “ (0 <= maxu) ” 
  &&  “ (maxu <= 128) ” 
  &&  “ (0 <= unique) ” 
  &&  “ (unique <= 128) ” 
  &&  “ (rows_well_formed_158 rows words_size_pre ) ” 
  &&  “ (problem_158_pre_z rows ) ” 
  &&  “ (best_prefix_state_158 rows i best_idx maxu ) ” 
  &&  “ (valid_string (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) ) ” 
  &&  “ (valid_string (row_payload_z_158 ((Znth (best_idx) (rows) ((@nil Z))))) ) ” 
  &&  “ ((string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX) ” 
  &&  “ ((string_length ((row_payload_z_158 ((Znth (best_idx) (rows) ((@nil Z))))))) < INT_MAX) ” 
  &&  “ ((Zlength (seen_l_2)) = 128) ”
  &&  (CharArray.full best_ptr ((string_length ((row_payload_z_158 ((Znth (best_idx) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_158 ((Znth (best_idx) (rows) ((@nil Z))))))) )
  **  (CharArray.full row_ptr ((string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) )
  **  (char_ptr_array2_missing_two_158 words_pre words_size_pre i row_ptr best_idx best_ptr rows )
  **  (((words_pre + (best_idx * sizeof(PTR) ) )) # Ptr  |-> best_ptr)
).

Definition find_max_entail_wit_13 := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (best_ptr: Z) (seen_l_2: (@list Z)) (i: Z) (best_idx: Z) (unique: Z) (maxu: Z) (PreH1 : (0 <= i)) (PreH2 : (i < words_size_pre)) (PreH3 : (0 < words_size_pre)) (PreH4 : (words_size_pre <= 100)) (PreH5 : (0 <= best_idx)) (PreH6 : (best_idx < words_size_pre)) (PreH7 : (i <> best_idx)) (PreH8 : (unique = (row_unique_count_z_158 ((Znth (i) (rows) ((@nil Z))))))) (PreH9 : (unique = maxu)) (PreH10 : (0 <= maxu)) (PreH11 : (maxu <= 128)) (PreH12 : (0 <= unique)) (PreH13 : (unique <= 128)) (PreH14 : (rows_well_formed_158 rows words_size_pre )) (PreH15 : (problem_158_pre_z rows )) (PreH16 : (best_prefix_state_158 rows i best_idx maxu )) (PreH17 : (valid_string (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) )) (PreH18 : (valid_string (row_payload_z_158 ((Znth (best_idx) (rows) ((@nil Z))))) )) (PreH19 : ((string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX)) (PreH20 : ((string_length ((row_payload_z_158 ((Znth (best_idx) (rows) ((@nil Z))))))) < INT_MAX)) (PreH21 : ((Zlength (seen_l_2)) = 128)) ,
  (char_ptr_array2_missing_two_158 words_pre words_size_pre i row_ptr best_idx best_ptr rows )
  **  (store_string row_ptr (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) )
  **  (((words_pre + (best_idx * sizeof(PTR) ) )) # Ptr  |-> best_ptr)
  **  (store_string best_ptr (row_payload_z_158 ((Znth (best_idx) (rows) ((@nil Z))))) )
  **  (IntArray.full ( &( "seen" ) ) 128 seen_l_2 )
|--
  EX (seen_l: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i < words_size_pre) ” 
  &&  “ (0 < words_size_pre) ” 
  &&  “ (words_size_pre <= 100) ” 
  &&  “ (0 <= best_idx) ” 
  &&  “ (best_idx < words_size_pre) ” 
  &&  “ (i <> best_idx) ” 
  &&  “ (unique = (row_unique_count_z_158 ((Znth (i) (rows) ((@nil Z)))))) ” 
  &&  “ (unique = maxu) ” 
  &&  “ (0 <= maxu) ” 
  &&  “ (maxu <= 128) ” 
  &&  “ (0 <= unique) ” 
  &&  “ (unique <= 128) ” 
  &&  “ (rows_well_formed_158 rows words_size_pre ) ” 
  &&  “ (problem_158_pre_z rows ) ” 
  &&  “ (best_prefix_state_158 rows i best_idx maxu ) ” 
  &&  “ (valid_string (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) ) ” 
  &&  “ (valid_string (row_payload_z_158 ((Znth (best_idx) (rows) ((@nil Z))))) ) ” 
  &&  “ ((string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX) ” 
  &&  “ ((string_length ((row_payload_z_158 ((Znth (best_idx) (rows) ((@nil Z))))))) < INT_MAX) ” 
  &&  “ ((Zlength (seen_l)) = 128) ”
  &&  (char_ptr_array2_missing_two_158 words_pre words_size_pre i row_ptr best_idx best_ptr rows )
  **  (store_string row_ptr (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) )
  **  (((words_pre + (best_idx * sizeof(PTR) ) )) # Ptr  |-> best_ptr)
  **  (store_string best_ptr (row_payload_z_158 ((Znth (best_idx) (rows) ((@nil Z))))) )
  **  (IntArray.full ( &( "seen" ) ) 128 seen_l )
.

Definition find_max_entail_wit_14 := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (best_ptr: Z) (seen_l_2: (@list Z)) (i: Z) (best_idx: Z) (unique: Z) (maxu: Z) (retval: Z) (PreH1 : (strcmp_result (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) (row_payload_z_158 ((Znth (best_idx) (rows) ((@nil Z))))) retval )) (PreH2 : (0 <= ((string_length ((row_payload_z_158 ((Znth (best_idx) (rows) ((@nil Z))))))) + 1 ))) (PreH3 : (0 <= ((string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) (PreH4 : (0 <= i)) (PreH5 : (i < words_size_pre)) (PreH6 : (0 < words_size_pre)) (PreH7 : (words_size_pre <= 100)) (PreH8 : (0 <= best_idx)) (PreH9 : (best_idx < words_size_pre)) (PreH10 : (i <> best_idx)) (PreH11 : (unique = (row_unique_count_z_158 ((Znth (i) (rows) ((@nil Z))))))) (PreH12 : (unique = maxu)) (PreH13 : (0 <= maxu)) (PreH14 : (maxu <= 128)) (PreH15 : (0 <= unique)) (PreH16 : (unique <= 128)) (PreH17 : (rows_well_formed_158 rows words_size_pre )) (PreH18 : (problem_158_pre_z rows )) (PreH19 : (best_prefix_state_158 rows i best_idx maxu )) (PreH20 : (valid_string (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) )) (PreH21 : (valid_string (row_payload_z_158 ((Znth (best_idx) (rows) ((@nil Z))))) )) (PreH22 : ((string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX)) (PreH23 : ((string_length ((row_payload_z_158 ((Znth (best_idx) (rows) ((@nil Z))))))) < INT_MAX)) (PreH24 : ((Zlength (seen_l_2)) = 128)) ,
  (store_string row_ptr (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) )
  **  (store_string best_ptr (row_payload_z_158 ((Znth (best_idx) (rows) ((@nil Z))))) )
  **  (char_ptr_array2_missing_two_158 words_pre words_size_pre i row_ptr best_idx best_ptr rows )
  **  (((words_pre + (best_idx * sizeof(PTR) ) )) # Ptr  |-> best_ptr)
  **  (IntArray.full ( &( "seen" ) ) 128 seen_l_2 )
|--
  EX (seen_l: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i < words_size_pre) ” 
  &&  “ (0 < words_size_pre) ” 
  &&  “ (words_size_pre <= 100) ” 
  &&  “ (0 <= best_idx) ” 
  &&  “ (best_idx < words_size_pre) ” 
  &&  “ (i <> best_idx) ” 
  &&  “ (unique = (row_unique_count_z_158 ((Znth (i) (rows) ((@nil Z)))))) ” 
  &&  “ (unique = maxu) ” 
  &&  “ (0 <= maxu) ” 
  &&  “ (maxu <= 128) ” 
  &&  “ (0 <= unique) ” 
  &&  “ (unique <= 128) ” 
  &&  “ (rows_well_formed_158 rows words_size_pre ) ” 
  &&  “ (problem_158_pre_z rows ) ” 
  &&  “ (best_prefix_state_158 rows i best_idx maxu ) ” 
  &&  “ (valid_string (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) ) ” 
  &&  “ (valid_string (row_payload_z_158 ((Znth (best_idx) (rows) ((@nil Z))))) ) ” 
  &&  “ ((string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX) ” 
  &&  “ ((string_length ((row_payload_z_158 ((Znth (best_idx) (rows) ((@nil Z))))))) < INT_MAX) ” 
  &&  “ (strcmp_result (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) (row_payload_z_158 ((Znth (best_idx) (rows) ((@nil Z))))) retval ) ” 
  &&  “ ((Zlength (seen_l)) = 128) ”
  &&  (char_ptr_array2_missing_two_158 words_pre words_size_pre i row_ptr best_idx best_ptr rows )
  **  (store_string row_ptr (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) )
  **  (((words_pre + (best_idx * sizeof(PTR) ) )) # Ptr  |-> best_ptr)
  **  (store_string best_ptr (row_payload_z_158 ((Znth (best_idx) (rows) ((@nil Z))))) )
  **  (IntArray.full ( &( "seen" ) ) 128 seen_l )
.

Definition find_max_entail_wit_15_1 := 
(
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (seen_l_2: (@list Z)) (ch: Z) (unique: Z) (maxu: Z) (best_idx: Z) (row_ptr: Z) (i: Z) (len: Z) (j: Z) (PreH1 : (i = best_idx)) (PreH2 : (unique = maxu)) (PreH3 : (unique <= maxu)) (PreH4 : (j >= len)) (PreH5 : (0 <= j)) (PreH6 : (j <= len)) (PreH7 : (0 <= i)) (PreH8 : (i < words_size_pre)) (PreH9 : (0 < words_size_pre)) (PreH10 : (words_size_pre <= 100)) (PreH11 : (0 <= best_idx)) (PreH12 : (best_idx < words_size_pre)) (PreH13 : (0 <= maxu)) (PreH14 : (maxu <= 128)) (PreH15 : (0 <= unique)) (PreH16 : (unique <= 128)) (PreH17 : (len = (string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))))) (PreH18 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = (len + 1 ))) (PreH19 : (valid_string (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) )) (PreH20 : (0 <= ch)) (PreH21 : (ch <= 127)) (PreH22 : ((Zlength (seen_l_2)) = 128)) (PreH23 : (rows_well_formed_158 rows words_size_pre )) (PreH24 : (problem_158_pre_z rows )) (PreH25 : (best_prefix_state_158 rows i best_idx maxu )) (PreH26 : (count_scan_state_158 (Znth (i) (rows) ((@nil Z))) j seen_l_2 unique )) ,
  (CharPtrArray2.missing_i words_pre words_size_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
  **  (IntArray.full ( &( "seen" ) ) 128 seen_l_2 )
|--
  EX (seen_l: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i < words_size_pre) ” 
  &&  “ (0 < words_size_pre) ” 
  &&  “ (words_size_pre <= 100) ” 
  &&  “ (0 <= best_idx) ” 
  &&  “ (best_idx < words_size_pre) ” 
  &&  “ (0 <= maxu) ” 
  &&  “ (maxu <= 128) ” 
  &&  “ (0 <= unique) ” 
  &&  “ (unique <= 128) ” 
  &&  “ (rows_well_formed_158 rows words_size_pre ) ” 
  &&  “ (problem_158_pre_z rows ) ” 
  &&  “ (best_prefix_state_158 rows (i + 1 ) best_idx maxu ) ” 
  &&  “ ((Zlength (seen_l)) = 128) ”
  &&  (CharPtrArray2.full words_pre words_size_pre rows )
  **  (IntArray.full ( &( "seen" ) ) 128 seen_l )
) \/
(
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (seen_l_2: (@list Z)) (ch: Z) (unique: Z) (maxu: Z) (best_idx: Z) (row_ptr: Z) (i: Z) (len: Z) (j: Z) (PreH1 : (0 <= (Zlength ((Znth (i) (rows) ((@nil Z))))))) (PreH2 : (i = best_idx)) (PreH3 : (unique = maxu)) (PreH4 : (unique <= maxu)) (PreH5 : (j >= len)) (PreH6 : (0 <= j)) (PreH7 : (j <= len)) (PreH8 : (0 <= i)) (PreH9 : (i < words_size_pre)) (PreH10 : (0 < words_size_pre)) (PreH11 : (words_size_pre <= 100)) (PreH12 : (0 <= best_idx)) (PreH13 : (best_idx < words_size_pre)) (PreH14 : (0 <= maxu)) (PreH15 : (maxu <= 128)) (PreH16 : (0 <= unique)) (PreH17 : (unique <= 128)) (PreH18 : (len = (string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))))) (PreH19 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = (len + 1 ))) (PreH20 : (valid_string (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) )) (PreH21 : (0 <= ch)) (PreH22 : (ch <= 127)) (PreH23 : ((Zlength (seen_l_2)) = 128)) (PreH24 : (rows_well_formed_158 rows words_size_pre )) (PreH25 : (problem_158_pre_z rows )) (PreH26 : (best_prefix_state_158 rows i best_idx maxu )) (PreH27 : (count_scan_state_158 (Znth (i) (rows) ((@nil Z))) j seen_l_2 unique )) ,
  (CharPtrArray2.missing_i words_pre words_size_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
|--
  “ (best_prefix_state_158 rows (i + 1 ) best_idx maxu ) ”
  &&  (CharPtrArray2.full words_pre words_size_pre rows )
).

Definition find_max_entail_wit_15_1_split_goal_1 := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (seen_l_2: (@list Z)) (ch: Z) (unique: Z) (maxu: Z) (best_idx: Z) (row_ptr: Z) (i: Z) (len: Z) (j: Z) (PreH1 : (0 <= (Zlength ((Znth (i) (rows) ((@nil Z))))))) (PreH2 : (i = best_idx)) (PreH3 : (unique = maxu)) (PreH4 : (unique <= maxu)) (PreH5 : (j >= len)) (PreH6 : (0 <= j)) (PreH7 : (j <= len)) (PreH8 : (0 <= i)) (PreH9 : (i < words_size_pre)) (PreH10 : (0 < words_size_pre)) (PreH11 : (words_size_pre <= 100)) (PreH12 : (0 <= best_idx)) (PreH13 : (best_idx < words_size_pre)) (PreH14 : (0 <= maxu)) (PreH15 : (maxu <= 128)) (PreH16 : (0 <= unique)) (PreH17 : (unique <= 128)) (PreH18 : (len = (string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))))) (PreH19 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = (len + 1 ))) (PreH20 : (valid_string (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) )) (PreH21 : (0 <= ch)) (PreH22 : (ch <= 127)) (PreH23 : ((Zlength (seen_l_2)) = 128)) (PreH24 : (rows_well_formed_158 rows words_size_pre )) (PreH25 : (problem_158_pre_z rows )) (PreH26 : (best_prefix_state_158 rows i best_idx maxu )) (PreH27 : (count_scan_state_158 (Znth (i) (rows) ((@nil Z))) j seen_l_2 unique )) ,
  (CharPtrArray2.missing_i words_pre words_size_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
|--
  “ (best_prefix_state_158 rows (i + 1 ) best_idx maxu ) ”
.

Definition find_max_entail_wit_15_1_split_goal_spatial := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (seen_l_2: (@list Z)) (ch: Z) (unique: Z) (maxu: Z) (best_idx: Z) (row_ptr: Z) (i: Z) (len: Z) (j: Z) (PreH1 : (0 <= (Zlength ((Znth (i) (rows) ((@nil Z))))))) (PreH2 : (i = best_idx)) (PreH3 : (unique = maxu)) (PreH4 : (unique <= maxu)) (PreH5 : (j >= len)) (PreH6 : (0 <= j)) (PreH7 : (j <= len)) (PreH8 : (0 <= i)) (PreH9 : (i < words_size_pre)) (PreH10 : (0 < words_size_pre)) (PreH11 : (words_size_pre <= 100)) (PreH12 : (0 <= best_idx)) (PreH13 : (best_idx < words_size_pre)) (PreH14 : (0 <= maxu)) (PreH15 : (maxu <= 128)) (PreH16 : (0 <= unique)) (PreH17 : (unique <= 128)) (PreH18 : (len = (string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))))) (PreH19 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = (len + 1 ))) (PreH20 : (valid_string (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) )) (PreH21 : (0 <= ch)) (PreH22 : (ch <= 127)) (PreH23 : ((Zlength (seen_l_2)) = 128)) (PreH24 : (rows_well_formed_158 rows words_size_pre )) (PreH25 : (problem_158_pre_z rows )) (PreH26 : (best_prefix_state_158 rows i best_idx maxu )) (PreH27 : (count_scan_state_158 (Znth (i) (rows) ((@nil Z))) j seen_l_2 unique )) ,
  (CharPtrArray2.missing_i words_pre words_size_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
|--
  (CharPtrArray2.full words_pre words_size_pre rows )
.

Definition find_max_entail_wit_15_2 := 
(
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (seen_l_2: (@list Z)) (ch: Z) (unique: Z) (maxu: Z) (best_idx: Z) (row_ptr: Z) (i: Z) (len: Z) (j: Z) (PreH1 : (unique <> maxu)) (PreH2 : (unique <= maxu)) (PreH3 : (j >= len)) (PreH4 : (0 <= j)) (PreH5 : (j <= len)) (PreH6 : (0 <= i)) (PreH7 : (i < words_size_pre)) (PreH8 : (0 < words_size_pre)) (PreH9 : (words_size_pre <= 100)) (PreH10 : (0 <= best_idx)) (PreH11 : (best_idx < words_size_pre)) (PreH12 : (0 <= maxu)) (PreH13 : (maxu <= 128)) (PreH14 : (0 <= unique)) (PreH15 : (unique <= 128)) (PreH16 : (len = (string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))))) (PreH17 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = (len + 1 ))) (PreH18 : (valid_string (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) )) (PreH19 : (0 <= ch)) (PreH20 : (ch <= 127)) (PreH21 : ((Zlength (seen_l_2)) = 128)) (PreH22 : (rows_well_formed_158 rows words_size_pre )) (PreH23 : (problem_158_pre_z rows )) (PreH24 : (best_prefix_state_158 rows i best_idx maxu )) (PreH25 : (count_scan_state_158 (Znth (i) (rows) ((@nil Z))) j seen_l_2 unique )) ,
  (CharPtrArray2.missing_i words_pre words_size_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
  **  (IntArray.full ( &( "seen" ) ) 128 seen_l_2 )
|--
  EX (seen_l: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i < words_size_pre) ” 
  &&  “ (0 < words_size_pre) ” 
  &&  “ (words_size_pre <= 100) ” 
  &&  “ (0 <= best_idx) ” 
  &&  “ (best_idx < words_size_pre) ” 
  &&  “ (0 <= maxu) ” 
  &&  “ (maxu <= 128) ” 
  &&  “ (0 <= unique) ” 
  &&  “ (unique <= 128) ” 
  &&  “ (rows_well_formed_158 rows words_size_pre ) ” 
  &&  “ (problem_158_pre_z rows ) ” 
  &&  “ (best_prefix_state_158 rows (i + 1 ) best_idx maxu ) ” 
  &&  “ ((Zlength (seen_l)) = 128) ”
  &&  (CharPtrArray2.full words_pre words_size_pre rows )
  **  (IntArray.full ( &( "seen" ) ) 128 seen_l )
) \/
(
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (seen_l_2: (@list Z)) (ch: Z) (unique: Z) (maxu: Z) (best_idx: Z) (row_ptr: Z) (i: Z) (len: Z) (j: Z) (PreH1 : (0 <= (Zlength ((Znth (i) (rows) ((@nil Z))))))) (PreH2 : (unique <> maxu)) (PreH3 : (unique <= maxu)) (PreH4 : (j >= len)) (PreH5 : (0 <= j)) (PreH6 : (j <= len)) (PreH7 : (0 <= i)) (PreH8 : (i < words_size_pre)) (PreH9 : (0 < words_size_pre)) (PreH10 : (words_size_pre <= 100)) (PreH11 : (0 <= best_idx)) (PreH12 : (best_idx < words_size_pre)) (PreH13 : (0 <= maxu)) (PreH14 : (maxu <= 128)) (PreH15 : (0 <= unique)) (PreH16 : (unique <= 128)) (PreH17 : (len = (string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))))) (PreH18 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = (len + 1 ))) (PreH19 : (valid_string (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) )) (PreH20 : (0 <= ch)) (PreH21 : (ch <= 127)) (PreH22 : ((Zlength (seen_l_2)) = 128)) (PreH23 : (rows_well_formed_158 rows words_size_pre )) (PreH24 : (problem_158_pre_z rows )) (PreH25 : (best_prefix_state_158 rows i best_idx maxu )) (PreH26 : (count_scan_state_158 (Znth (i) (rows) ((@nil Z))) j seen_l_2 unique )) ,
  (CharPtrArray2.missing_i words_pre words_size_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
|--
  “ (best_prefix_state_158 rows (i + 1 ) best_idx maxu ) ”
  &&  (CharPtrArray2.full words_pre words_size_pre rows )
).

Definition find_max_entail_wit_15_2_split_goal_1 := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (seen_l_2: (@list Z)) (ch: Z) (unique: Z) (maxu: Z) (best_idx: Z) (row_ptr: Z) (i: Z) (len: Z) (j: Z) (PreH1 : (0 <= (Zlength ((Znth (i) (rows) ((@nil Z))))))) (PreH2 : (unique <> maxu)) (PreH3 : (unique <= maxu)) (PreH4 : (j >= len)) (PreH5 : (0 <= j)) (PreH6 : (j <= len)) (PreH7 : (0 <= i)) (PreH8 : (i < words_size_pre)) (PreH9 : (0 < words_size_pre)) (PreH10 : (words_size_pre <= 100)) (PreH11 : (0 <= best_idx)) (PreH12 : (best_idx < words_size_pre)) (PreH13 : (0 <= maxu)) (PreH14 : (maxu <= 128)) (PreH15 : (0 <= unique)) (PreH16 : (unique <= 128)) (PreH17 : (len = (string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))))) (PreH18 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = (len + 1 ))) (PreH19 : (valid_string (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) )) (PreH20 : (0 <= ch)) (PreH21 : (ch <= 127)) (PreH22 : ((Zlength (seen_l_2)) = 128)) (PreH23 : (rows_well_formed_158 rows words_size_pre )) (PreH24 : (problem_158_pre_z rows )) (PreH25 : (best_prefix_state_158 rows i best_idx maxu )) (PreH26 : (count_scan_state_158 (Znth (i) (rows) ((@nil Z))) j seen_l_2 unique )) ,
  (CharPtrArray2.missing_i words_pre words_size_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
|--
  “ (best_prefix_state_158 rows (i + 1 ) best_idx maxu ) ”
.

Definition find_max_entail_wit_15_2_split_goal_spatial := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (seen_l_2: (@list Z)) (ch: Z) (unique: Z) (maxu: Z) (best_idx: Z) (row_ptr: Z) (i: Z) (len: Z) (j: Z) (PreH1 : (0 <= (Zlength ((Znth (i) (rows) ((@nil Z))))))) (PreH2 : (unique <> maxu)) (PreH3 : (unique <= maxu)) (PreH4 : (j >= len)) (PreH5 : (0 <= j)) (PreH6 : (j <= len)) (PreH7 : (0 <= i)) (PreH8 : (i < words_size_pre)) (PreH9 : (0 < words_size_pre)) (PreH10 : (words_size_pre <= 100)) (PreH11 : (0 <= best_idx)) (PreH12 : (best_idx < words_size_pre)) (PreH13 : (0 <= maxu)) (PreH14 : (maxu <= 128)) (PreH15 : (0 <= unique)) (PreH16 : (unique <= 128)) (PreH17 : (len = (string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))))) (PreH18 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = (len + 1 ))) (PreH19 : (valid_string (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) )) (PreH20 : (0 <= ch)) (PreH21 : (ch <= 127)) (PreH22 : ((Zlength (seen_l_2)) = 128)) (PreH23 : (rows_well_formed_158 rows words_size_pre )) (PreH24 : (problem_158_pre_z rows )) (PreH25 : (best_prefix_state_158 rows i best_idx maxu )) (PreH26 : (count_scan_state_158 (Znth (i) (rows) ((@nil Z))) j seen_l_2 unique )) ,
  (CharPtrArray2.missing_i words_pre words_size_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
|--
  (CharPtrArray2.full words_pre words_size_pre rows )
.

Definition find_max_entail_wit_15_3 := 
(
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (best_ptr: Z) (seen_l_2: (@list Z)) (i: Z) (best_idx: Z) (unique: Z) (maxu: Z) (cmp: Z) (PreH1 : (cmp >= 0)) (PreH2 : (0 <= i)) (PreH3 : (i < words_size_pre)) (PreH4 : (0 < words_size_pre)) (PreH5 : (words_size_pre <= 100)) (PreH6 : (0 <= best_idx)) (PreH7 : (best_idx < words_size_pre)) (PreH8 : (i <> best_idx)) (PreH9 : (unique = (row_unique_count_z_158 ((Znth (i) (rows) ((@nil Z))))))) (PreH10 : (unique = maxu)) (PreH11 : (0 <= maxu)) (PreH12 : (maxu <= 128)) (PreH13 : (0 <= unique)) (PreH14 : (unique <= 128)) (PreH15 : (rows_well_formed_158 rows words_size_pre )) (PreH16 : (problem_158_pre_z rows )) (PreH17 : (best_prefix_state_158 rows i best_idx maxu )) (PreH18 : (valid_string (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) )) (PreH19 : (valid_string (row_payload_z_158 ((Znth (best_idx) (rows) ((@nil Z))))) )) (PreH20 : ((string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX)) (PreH21 : ((string_length ((row_payload_z_158 ((Znth (best_idx) (rows) ((@nil Z))))))) < INT_MAX)) (PreH22 : (strcmp_result (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) (row_payload_z_158 ((Znth (best_idx) (rows) ((@nil Z))))) cmp )) (PreH23 : ((Zlength (seen_l_2)) = 128)) ,
  (char_ptr_array2_missing_two_158 words_pre words_size_pre i row_ptr best_idx best_ptr rows )
  **  (store_string row_ptr (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) )
  **  (((words_pre + (best_idx * sizeof(PTR) ) )) # Ptr  |-> best_ptr)
  **  (store_string best_ptr (row_payload_z_158 ((Znth (best_idx) (rows) ((@nil Z))))) )
  **  (IntArray.full ( &( "seen" ) ) 128 seen_l_2 )
|--
  EX (seen_l: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i < words_size_pre) ” 
  &&  “ (0 < words_size_pre) ” 
  &&  “ (words_size_pre <= 100) ” 
  &&  “ (0 <= best_idx) ” 
  &&  “ (best_idx < words_size_pre) ” 
  &&  “ (0 <= maxu) ” 
  &&  “ (maxu <= 128) ” 
  &&  “ (0 <= unique) ” 
  &&  “ (unique <= 128) ” 
  &&  “ (rows_well_formed_158 rows words_size_pre ) ” 
  &&  “ (problem_158_pre_z rows ) ” 
  &&  “ (best_prefix_state_158 rows (i + 1 ) best_idx maxu ) ” 
  &&  “ ((Zlength (seen_l)) = 128) ”
  &&  (CharPtrArray2.full words_pre words_size_pre rows )
  **  (IntArray.full ( &( "seen" ) ) 128 seen_l )
) \/
(
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (best_ptr: Z) (seen_l_2: (@list Z)) (i: Z) (best_idx: Z) (unique: Z) (maxu: Z) (cmp: Z) (PreH1 : (0 <= ((string_length ((row_payload_z_158 ((Znth (best_idx) (rows) ((@nil Z))))))) + 1 ))) (PreH2 : (0 <= ((string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) (PreH3 : (cmp >= 0)) (PreH4 : (0 <= i)) (PreH5 : (i < words_size_pre)) (PreH6 : (0 < words_size_pre)) (PreH7 : (words_size_pre <= 100)) (PreH8 : (0 <= best_idx)) (PreH9 : (best_idx < words_size_pre)) (PreH10 : (i <> best_idx)) (PreH11 : (unique = (row_unique_count_z_158 ((Znth (i) (rows) ((@nil Z))))))) (PreH12 : (unique = maxu)) (PreH13 : (0 <= maxu)) (PreH14 : (maxu <= 128)) (PreH15 : (0 <= unique)) (PreH16 : (unique <= 128)) (PreH17 : (rows_well_formed_158 rows words_size_pre )) (PreH18 : (problem_158_pre_z rows )) (PreH19 : (best_prefix_state_158 rows i best_idx maxu )) (PreH20 : (valid_string (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) )) (PreH21 : (valid_string (row_payload_z_158 ((Znth (best_idx) (rows) ((@nil Z))))) )) (PreH22 : ((string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX)) (PreH23 : ((string_length ((row_payload_z_158 ((Znth (best_idx) (rows) ((@nil Z))))))) < INT_MAX)) (PreH24 : (strcmp_result (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) (row_payload_z_158 ((Znth (best_idx) (rows) ((@nil Z))))) cmp )) (PreH25 : ((Zlength (seen_l_2)) = 128)) ,
  (CharArray.full best_ptr ((string_length ((row_payload_z_158 ((Znth (best_idx) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_158 ((Znth (best_idx) (rows) ((@nil Z))))))) )
  **  (CharArray.full row_ptr ((string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) )
  **  (char_ptr_array2_missing_two_158 words_pre words_size_pre i row_ptr best_idx best_ptr rows )
  **  (((words_pre + (best_idx * sizeof(PTR) ) )) # Ptr  |-> best_ptr)
|--
  “ (best_prefix_state_158 rows (i + 1 ) best_idx maxu ) ”
  &&  (CharPtrArray2.full words_pre words_size_pre rows )
).

Definition find_max_entail_wit_15_3_split_goal_1 := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (best_ptr: Z) (seen_l_2: (@list Z)) (i: Z) (best_idx: Z) (unique: Z) (maxu: Z) (cmp: Z) (PreH1 : (0 <= ((string_length ((row_payload_z_158 ((Znth (best_idx) (rows) ((@nil Z))))))) + 1 ))) (PreH2 : (0 <= ((string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) (PreH3 : (cmp >= 0)) (PreH4 : (0 <= i)) (PreH5 : (i < words_size_pre)) (PreH6 : (0 < words_size_pre)) (PreH7 : (words_size_pre <= 100)) (PreH8 : (0 <= best_idx)) (PreH9 : (best_idx < words_size_pre)) (PreH10 : (i <> best_idx)) (PreH11 : (unique = (row_unique_count_z_158 ((Znth (i) (rows) ((@nil Z))))))) (PreH12 : (unique = maxu)) (PreH13 : (0 <= maxu)) (PreH14 : (maxu <= 128)) (PreH15 : (0 <= unique)) (PreH16 : (unique <= 128)) (PreH17 : (rows_well_formed_158 rows words_size_pre )) (PreH18 : (problem_158_pre_z rows )) (PreH19 : (best_prefix_state_158 rows i best_idx maxu )) (PreH20 : (valid_string (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) )) (PreH21 : (valid_string (row_payload_z_158 ((Znth (best_idx) (rows) ((@nil Z))))) )) (PreH22 : ((string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX)) (PreH23 : ((string_length ((row_payload_z_158 ((Znth (best_idx) (rows) ((@nil Z))))))) < INT_MAX)) (PreH24 : (strcmp_result (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) (row_payload_z_158 ((Znth (best_idx) (rows) ((@nil Z))))) cmp )) (PreH25 : ((Zlength (seen_l_2)) = 128)) ,
  (CharArray.full best_ptr ((string_length ((row_payload_z_158 ((Znth (best_idx) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_158 ((Znth (best_idx) (rows) ((@nil Z))))))) )
  **  (CharArray.full row_ptr ((string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) )
  **  (char_ptr_array2_missing_two_158 words_pre words_size_pre i row_ptr best_idx best_ptr rows )
  **  (((words_pre + (best_idx * sizeof(PTR) ) )) # Ptr  |-> best_ptr)
|--
  “ (best_prefix_state_158 rows (i + 1 ) best_idx maxu ) ”
.

Definition find_max_entail_wit_15_3_split_goal_spatial := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (best_ptr: Z) (seen_l_2: (@list Z)) (i: Z) (best_idx: Z) (unique: Z) (maxu: Z) (cmp: Z) (PreH1 : (0 <= ((string_length ((row_payload_z_158 ((Znth (best_idx) (rows) ((@nil Z))))))) + 1 ))) (PreH2 : (0 <= ((string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) (PreH3 : (cmp >= 0)) (PreH4 : (0 <= i)) (PreH5 : (i < words_size_pre)) (PreH6 : (0 < words_size_pre)) (PreH7 : (words_size_pre <= 100)) (PreH8 : (0 <= best_idx)) (PreH9 : (best_idx < words_size_pre)) (PreH10 : (i <> best_idx)) (PreH11 : (unique = (row_unique_count_z_158 ((Znth (i) (rows) ((@nil Z))))))) (PreH12 : (unique = maxu)) (PreH13 : (0 <= maxu)) (PreH14 : (maxu <= 128)) (PreH15 : (0 <= unique)) (PreH16 : (unique <= 128)) (PreH17 : (rows_well_formed_158 rows words_size_pre )) (PreH18 : (problem_158_pre_z rows )) (PreH19 : (best_prefix_state_158 rows i best_idx maxu )) (PreH20 : (valid_string (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) )) (PreH21 : (valid_string (row_payload_z_158 ((Znth (best_idx) (rows) ((@nil Z))))) )) (PreH22 : ((string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX)) (PreH23 : ((string_length ((row_payload_z_158 ((Znth (best_idx) (rows) ((@nil Z))))))) < INT_MAX)) (PreH24 : (strcmp_result (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) (row_payload_z_158 ((Znth (best_idx) (rows) ((@nil Z))))) cmp )) (PreH25 : ((Zlength (seen_l_2)) = 128)) ,
  (CharArray.full best_ptr ((string_length ((row_payload_z_158 ((Znth (best_idx) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_158 ((Znth (best_idx) (rows) ((@nil Z))))))) )
  **  (CharArray.full row_ptr ((string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) )
  **  (char_ptr_array2_missing_two_158 words_pre words_size_pre i row_ptr best_idx best_ptr rows )
  **  (((words_pre + (best_idx * sizeof(PTR) ) )) # Ptr  |-> best_ptr)
|--
  (CharPtrArray2.full words_pre words_size_pre rows )
.

Definition find_max_entail_wit_15_4 := 
(
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (best_ptr: Z) (seen_l_2: (@list Z)) (i: Z) (best_idx: Z) (unique: Z) (maxu: Z) (cmp: Z) (PreH1 : (cmp < 0)) (PreH2 : (0 <= i)) (PreH3 : (i < words_size_pre)) (PreH4 : (0 < words_size_pre)) (PreH5 : (words_size_pre <= 100)) (PreH6 : (0 <= best_idx)) (PreH7 : (best_idx < words_size_pre)) (PreH8 : (i <> best_idx)) (PreH9 : (unique = (row_unique_count_z_158 ((Znth (i) (rows) ((@nil Z))))))) (PreH10 : (unique = maxu)) (PreH11 : (0 <= maxu)) (PreH12 : (maxu <= 128)) (PreH13 : (0 <= unique)) (PreH14 : (unique <= 128)) (PreH15 : (rows_well_formed_158 rows words_size_pre )) (PreH16 : (problem_158_pre_z rows )) (PreH17 : (best_prefix_state_158 rows i best_idx maxu )) (PreH18 : (valid_string (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) )) (PreH19 : (valid_string (row_payload_z_158 ((Znth (best_idx) (rows) ((@nil Z))))) )) (PreH20 : ((string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX)) (PreH21 : ((string_length ((row_payload_z_158 ((Znth (best_idx) (rows) ((@nil Z))))))) < INT_MAX)) (PreH22 : (strcmp_result (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) (row_payload_z_158 ((Znth (best_idx) (rows) ((@nil Z))))) cmp )) (PreH23 : ((Zlength (seen_l_2)) = 128)) ,
  (char_ptr_array2_missing_two_158 words_pre words_size_pre i row_ptr best_idx best_ptr rows )
  **  (store_string row_ptr (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) )
  **  (((words_pre + (best_idx * sizeof(PTR) ) )) # Ptr  |-> best_ptr)
  **  (store_string best_ptr (row_payload_z_158 ((Znth (best_idx) (rows) ((@nil Z))))) )
  **  (IntArray.full ( &( "seen" ) ) 128 seen_l_2 )
|--
  EX (seen_l: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i < words_size_pre) ” 
  &&  “ (0 < words_size_pre) ” 
  &&  “ (words_size_pre <= 100) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < words_size_pre) ” 
  &&  “ (0 <= maxu) ” 
  &&  “ (maxu <= 128) ” 
  &&  “ (0 <= unique) ” 
  &&  “ (unique <= 128) ” 
  &&  “ (rows_well_formed_158 rows words_size_pre ) ” 
  &&  “ (problem_158_pre_z rows ) ” 
  &&  “ (best_prefix_state_158 rows (i + 1 ) i maxu ) ” 
  &&  “ ((Zlength (seen_l)) = 128) ”
  &&  (CharPtrArray2.full words_pre words_size_pre rows )
  **  (IntArray.full ( &( "seen" ) ) 128 seen_l )
) \/
(
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (best_ptr: Z) (seen_l_2: (@list Z)) (i: Z) (best_idx: Z) (unique: Z) (maxu: Z) (cmp: Z) (PreH1 : (0 <= ((string_length ((row_payload_z_158 ((Znth (best_idx) (rows) ((@nil Z))))))) + 1 ))) (PreH2 : (0 <= ((string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) (PreH3 : (cmp < 0)) (PreH4 : (0 <= i)) (PreH5 : (i < words_size_pre)) (PreH6 : (0 < words_size_pre)) (PreH7 : (words_size_pre <= 100)) (PreH8 : (0 <= best_idx)) (PreH9 : (best_idx < words_size_pre)) (PreH10 : (i <> best_idx)) (PreH11 : (unique = (row_unique_count_z_158 ((Znth (i) (rows) ((@nil Z))))))) (PreH12 : (unique = maxu)) (PreH13 : (0 <= maxu)) (PreH14 : (maxu <= 128)) (PreH15 : (0 <= unique)) (PreH16 : (unique <= 128)) (PreH17 : (rows_well_formed_158 rows words_size_pre )) (PreH18 : (problem_158_pre_z rows )) (PreH19 : (best_prefix_state_158 rows i best_idx maxu )) (PreH20 : (valid_string (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) )) (PreH21 : (valid_string (row_payload_z_158 ((Znth (best_idx) (rows) ((@nil Z))))) )) (PreH22 : ((string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX)) (PreH23 : ((string_length ((row_payload_z_158 ((Znth (best_idx) (rows) ((@nil Z))))))) < INT_MAX)) (PreH24 : (strcmp_result (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) (row_payload_z_158 ((Znth (best_idx) (rows) ((@nil Z))))) cmp )) (PreH25 : ((Zlength (seen_l_2)) = 128)) ,
  (CharArray.full best_ptr ((string_length ((row_payload_z_158 ((Znth (best_idx) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_158 ((Znth (best_idx) (rows) ((@nil Z))))))) )
  **  (CharArray.full row_ptr ((string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) )
  **  (char_ptr_array2_missing_two_158 words_pre words_size_pre i row_ptr best_idx best_ptr rows )
  **  (((words_pre + (best_idx * sizeof(PTR) ) )) # Ptr  |-> best_ptr)
|--
  “ (best_prefix_state_158 rows (i + 1 ) i maxu ) ”
  &&  (CharPtrArray2.full words_pre words_size_pre rows )
).

Definition find_max_entail_wit_15_4_split_goal_1 := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (best_ptr: Z) (seen_l_2: (@list Z)) (i: Z) (best_idx: Z) (unique: Z) (maxu: Z) (cmp: Z) (PreH1 : (0 <= ((string_length ((row_payload_z_158 ((Znth (best_idx) (rows) ((@nil Z))))))) + 1 ))) (PreH2 : (0 <= ((string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) (PreH3 : (cmp < 0)) (PreH4 : (0 <= i)) (PreH5 : (i < words_size_pre)) (PreH6 : (0 < words_size_pre)) (PreH7 : (words_size_pre <= 100)) (PreH8 : (0 <= best_idx)) (PreH9 : (best_idx < words_size_pre)) (PreH10 : (i <> best_idx)) (PreH11 : (unique = (row_unique_count_z_158 ((Znth (i) (rows) ((@nil Z))))))) (PreH12 : (unique = maxu)) (PreH13 : (0 <= maxu)) (PreH14 : (maxu <= 128)) (PreH15 : (0 <= unique)) (PreH16 : (unique <= 128)) (PreH17 : (rows_well_formed_158 rows words_size_pre )) (PreH18 : (problem_158_pre_z rows )) (PreH19 : (best_prefix_state_158 rows i best_idx maxu )) (PreH20 : (valid_string (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) )) (PreH21 : (valid_string (row_payload_z_158 ((Znth (best_idx) (rows) ((@nil Z))))) )) (PreH22 : ((string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX)) (PreH23 : ((string_length ((row_payload_z_158 ((Znth (best_idx) (rows) ((@nil Z))))))) < INT_MAX)) (PreH24 : (strcmp_result (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) (row_payload_z_158 ((Znth (best_idx) (rows) ((@nil Z))))) cmp )) (PreH25 : ((Zlength (seen_l_2)) = 128)) ,
  (CharArray.full best_ptr ((string_length ((row_payload_z_158 ((Znth (best_idx) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_158 ((Znth (best_idx) (rows) ((@nil Z))))))) )
  **  (CharArray.full row_ptr ((string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) )
  **  (char_ptr_array2_missing_two_158 words_pre words_size_pre i row_ptr best_idx best_ptr rows )
  **  (((words_pre + (best_idx * sizeof(PTR) ) )) # Ptr  |-> best_ptr)
|--
  “ (best_prefix_state_158 rows (i + 1 ) i maxu ) ”
.

Definition find_max_entail_wit_15_4_split_goal_spatial := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (best_ptr: Z) (seen_l_2: (@list Z)) (i: Z) (best_idx: Z) (unique: Z) (maxu: Z) (cmp: Z) (PreH1 : (0 <= ((string_length ((row_payload_z_158 ((Znth (best_idx) (rows) ((@nil Z))))))) + 1 ))) (PreH2 : (0 <= ((string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) (PreH3 : (cmp < 0)) (PreH4 : (0 <= i)) (PreH5 : (i < words_size_pre)) (PreH6 : (0 < words_size_pre)) (PreH7 : (words_size_pre <= 100)) (PreH8 : (0 <= best_idx)) (PreH9 : (best_idx < words_size_pre)) (PreH10 : (i <> best_idx)) (PreH11 : (unique = (row_unique_count_z_158 ((Znth (i) (rows) ((@nil Z))))))) (PreH12 : (unique = maxu)) (PreH13 : (0 <= maxu)) (PreH14 : (maxu <= 128)) (PreH15 : (0 <= unique)) (PreH16 : (unique <= 128)) (PreH17 : (rows_well_formed_158 rows words_size_pre )) (PreH18 : (problem_158_pre_z rows )) (PreH19 : (best_prefix_state_158 rows i best_idx maxu )) (PreH20 : (valid_string (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) )) (PreH21 : (valid_string (row_payload_z_158 ((Znth (best_idx) (rows) ((@nil Z))))) )) (PreH22 : ((string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX)) (PreH23 : ((string_length ((row_payload_z_158 ((Znth (best_idx) (rows) ((@nil Z))))))) < INT_MAX)) (PreH24 : (strcmp_result (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) (row_payload_z_158 ((Znth (best_idx) (rows) ((@nil Z))))) cmp )) (PreH25 : ((Zlength (seen_l_2)) = 128)) ,
  (CharArray.full best_ptr ((string_length ((row_payload_z_158 ((Znth (best_idx) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_158 ((Znth (best_idx) (rows) ((@nil Z))))))) )
  **  (CharArray.full row_ptr ((string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) )
  **  (char_ptr_array2_missing_two_158 words_pre words_size_pre i row_ptr best_idx best_ptr rows )
  **  (((words_pre + (best_idx * sizeof(PTR) ) )) # Ptr  |-> best_ptr)
|--
  (CharPtrArray2.full words_pre words_size_pre rows )
.

Definition find_max_entail_wit_15_5 := 
(
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (seen_l_2: (@list Z)) (ch: Z) (unique: Z) (maxu: Z) (best_idx: Z) (row_ptr: Z) (i: Z) (len: Z) (j: Z) (PreH1 : (unique > maxu)) (PreH2 : (j >= len)) (PreH3 : (0 <= j)) (PreH4 : (j <= len)) (PreH5 : (0 <= i)) (PreH6 : (i < words_size_pre)) (PreH7 : (0 < words_size_pre)) (PreH8 : (words_size_pre <= 100)) (PreH9 : (0 <= best_idx)) (PreH10 : (best_idx < words_size_pre)) (PreH11 : (0 <= maxu)) (PreH12 : (maxu <= 128)) (PreH13 : (0 <= unique)) (PreH14 : (unique <= 128)) (PreH15 : (len = (string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))))) (PreH16 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = (len + 1 ))) (PreH17 : (valid_string (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) )) (PreH18 : (0 <= ch)) (PreH19 : (ch <= 127)) (PreH20 : ((Zlength (seen_l_2)) = 128)) (PreH21 : (rows_well_formed_158 rows words_size_pre )) (PreH22 : (problem_158_pre_z rows )) (PreH23 : (best_prefix_state_158 rows i best_idx maxu )) (PreH24 : (count_scan_state_158 (Znth (i) (rows) ((@nil Z))) j seen_l_2 unique )) ,
  (CharPtrArray2.missing_i words_pre words_size_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
  **  (IntArray.full ( &( "seen" ) ) 128 seen_l_2 )
|--
  EX (seen_l: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i < words_size_pre) ” 
  &&  “ (0 < words_size_pre) ” 
  &&  “ (words_size_pre <= 100) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < words_size_pre) ” 
  &&  “ (0 <= unique) ” 
  &&  “ (unique <= 128) ” 
  &&  “ (0 <= unique) ” 
  &&  “ (unique <= 128) ” 
  &&  “ (rows_well_formed_158 rows words_size_pre ) ” 
  &&  “ (problem_158_pre_z rows ) ” 
  &&  “ (best_prefix_state_158 rows (i + 1 ) i unique ) ” 
  &&  “ ((Zlength (seen_l)) = 128) ”
  &&  (CharPtrArray2.full words_pre words_size_pre rows )
  **  (IntArray.full ( &( "seen" ) ) 128 seen_l )
) \/
(
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (seen_l_2: (@list Z)) (ch: Z) (unique: Z) (maxu: Z) (best_idx: Z) (row_ptr: Z) (i: Z) (len: Z) (j: Z) (PreH1 : (0 <= (Zlength ((Znth (i) (rows) ((@nil Z))))))) (PreH2 : (unique > maxu)) (PreH3 : (j >= len)) (PreH4 : (0 <= j)) (PreH5 : (j <= len)) (PreH6 : (0 <= i)) (PreH7 : (i < words_size_pre)) (PreH8 : (0 < words_size_pre)) (PreH9 : (words_size_pre <= 100)) (PreH10 : (0 <= best_idx)) (PreH11 : (best_idx < words_size_pre)) (PreH12 : (0 <= maxu)) (PreH13 : (maxu <= 128)) (PreH14 : (0 <= unique)) (PreH15 : (unique <= 128)) (PreH16 : (len = (string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))))) (PreH17 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = (len + 1 ))) (PreH18 : (valid_string (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) )) (PreH19 : (0 <= ch)) (PreH20 : (ch <= 127)) (PreH21 : ((Zlength (seen_l_2)) = 128)) (PreH22 : (rows_well_formed_158 rows words_size_pre )) (PreH23 : (problem_158_pre_z rows )) (PreH24 : (best_prefix_state_158 rows i best_idx maxu )) (PreH25 : (count_scan_state_158 (Znth (i) (rows) ((@nil Z))) j seen_l_2 unique )) ,
  (CharPtrArray2.missing_i words_pre words_size_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
|--
  “ (best_prefix_state_158 rows (i + 1 ) i unique ) ”
  &&  (CharPtrArray2.full words_pre words_size_pre rows )
).

Definition find_max_entail_wit_15_5_split_goal_1 := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (seen_l_2: (@list Z)) (ch: Z) (unique: Z) (maxu: Z) (best_idx: Z) (row_ptr: Z) (i: Z) (len: Z) (j: Z) (PreH1 : (0 <= (Zlength ((Znth (i) (rows) ((@nil Z))))))) (PreH2 : (unique > maxu)) (PreH3 : (j >= len)) (PreH4 : (0 <= j)) (PreH5 : (j <= len)) (PreH6 : (0 <= i)) (PreH7 : (i < words_size_pre)) (PreH8 : (0 < words_size_pre)) (PreH9 : (words_size_pre <= 100)) (PreH10 : (0 <= best_idx)) (PreH11 : (best_idx < words_size_pre)) (PreH12 : (0 <= maxu)) (PreH13 : (maxu <= 128)) (PreH14 : (0 <= unique)) (PreH15 : (unique <= 128)) (PreH16 : (len = (string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))))) (PreH17 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = (len + 1 ))) (PreH18 : (valid_string (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) )) (PreH19 : (0 <= ch)) (PreH20 : (ch <= 127)) (PreH21 : ((Zlength (seen_l_2)) = 128)) (PreH22 : (rows_well_formed_158 rows words_size_pre )) (PreH23 : (problem_158_pre_z rows )) (PreH24 : (best_prefix_state_158 rows i best_idx maxu )) (PreH25 : (count_scan_state_158 (Znth (i) (rows) ((@nil Z))) j seen_l_2 unique )) ,
  (CharPtrArray2.missing_i words_pre words_size_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
|--
  “ (best_prefix_state_158 rows (i + 1 ) i unique ) ”
.

Definition find_max_entail_wit_15_5_split_goal_spatial := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (seen_l_2: (@list Z)) (ch: Z) (unique: Z) (maxu: Z) (best_idx: Z) (row_ptr: Z) (i: Z) (len: Z) (j: Z) (PreH1 : (0 <= (Zlength ((Znth (i) (rows) ((@nil Z))))))) (PreH2 : (unique > maxu)) (PreH3 : (j >= len)) (PreH4 : (0 <= j)) (PreH5 : (j <= len)) (PreH6 : (0 <= i)) (PreH7 : (i < words_size_pre)) (PreH8 : (0 < words_size_pre)) (PreH9 : (words_size_pre <= 100)) (PreH10 : (0 <= best_idx)) (PreH11 : (best_idx < words_size_pre)) (PreH12 : (0 <= maxu)) (PreH13 : (maxu <= 128)) (PreH14 : (0 <= unique)) (PreH15 : (unique <= 128)) (PreH16 : (len = (string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))))) (PreH17 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = (len + 1 ))) (PreH18 : (valid_string (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) )) (PreH19 : (0 <= ch)) (PreH20 : (ch <= 127)) (PreH21 : ((Zlength (seen_l_2)) = 128)) (PreH22 : (rows_well_formed_158 rows words_size_pre )) (PreH23 : (problem_158_pre_z rows )) (PreH24 : (best_prefix_state_158 rows i best_idx maxu )) (PreH25 : (count_scan_state_158 (Znth (i) (rows) ((@nil Z))) j seen_l_2 unique )) ,
  (CharPtrArray2.missing_i words_pre words_size_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
|--
  (CharPtrArray2.full words_pre words_size_pre rows )
.

Definition find_max_entail_wit_16 := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (seen_l_2: (@list Z)) (i: Z) (best_idx: Z) (maxu: Z) (unique: Z) (PreH1 : (0 <= i)) (PreH2 : (i < words_size_pre)) (PreH3 : (0 < words_size_pre)) (PreH4 : (words_size_pre <= 100)) (PreH5 : (0 <= best_idx)) (PreH6 : (best_idx < words_size_pre)) (PreH7 : (0 <= maxu)) (PreH8 : (maxu <= 128)) (PreH9 : (0 <= unique)) (PreH10 : (unique <= 128)) (PreH11 : (rows_well_formed_158 rows words_size_pre )) (PreH12 : (problem_158_pre_z rows )) (PreH13 : (best_prefix_state_158 rows (i + 1 ) best_idx maxu )) (PreH14 : ((Zlength (seen_l_2)) = 128)) ,
  (CharPtrArray2.full words_pre words_size_pre rows )
  **  (IntArray.full ( &( "seen" ) ) 128 seen_l_2 )
|--
  EX (seen_l: (@list Z)) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= words_size_pre) ” 
  &&  “ (0 < words_size_pre) ” 
  &&  “ (words_size_pre <= 100) ” 
  &&  “ (0 <= best_idx) ” 
  &&  “ (best_idx < words_size_pre) ” 
  &&  “ (0 <= maxu) ” 
  &&  “ (maxu <= 128) ” 
  &&  “ (0 <= unique) ” 
  &&  “ (unique <= 128) ” 
  &&  “ (rows_well_formed_158 rows words_size_pre ) ” 
  &&  “ (problem_158_pre_z rows ) ” 
  &&  “ (best_prefix_state_158 rows (i + 1 ) best_idx maxu ) ” 
  &&  “ ((Zlength (seen_l)) = 128) ”
  &&  (CharPtrArray2.full words_pre words_size_pre rows )
  **  (IntArray.full ( &( "seen" ) ) 128 seen_l )
.

Definition find_max_entail_wit_17 := 
(
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (seen_l_2: (@list Z)) (unique: Z) (maxu: Z) (best_idx: Z) (i: Z) (PreH1 : (i >= words_size_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= words_size_pre)) (PreH4 : (0 < words_size_pre)) (PreH5 : (words_size_pre <= 100)) (PreH6 : (0 <= best_idx)) (PreH7 : (best_idx < words_size_pre)) (PreH8 : (0 <= maxu)) (PreH9 : (maxu <= 128)) (PreH10 : (0 <= unique)) (PreH11 : (unique <= 128)) (PreH12 : (rows_well_formed_158 rows words_size_pre )) (PreH13 : (problem_158_pre_z rows )) (PreH14 : (best_prefix_state_158 rows i best_idx maxu )) (PreH15 : ((Zlength (seen_l_2)) = 128)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  (CharPtrArray2.full words_pre words_size_pre rows )
  **  (IntArray.full ( &( "seen" ) ) 128 seen_l_2 )
|--
  EX (row_ptr: Z)  (seen_l: (@list Z)) ,
  “ (0 <= best_idx) ” 
  &&  “ (best_idx < words_size_pre) ” 
  &&  “ (0 <= maxu) ” 
  &&  “ (maxu <= 128) ” 
  &&  “ (0 <= unique) ” 
  &&  “ (unique <= 128) ” 
  &&  “ (rows_well_formed_158 rows words_size_pre ) ” 
  &&  “ (problem_158_pre_z rows ) ” 
  &&  “ (best_prefix_state_158 rows words_size_pre best_idx maxu ) ” 
  &&  “ (problem_158_spec_z rows best_idx ) ” 
  &&  “ ((Zlength (seen_l)) = 128) ”
  &&  ((( &( "i" ) )) # Int  |-> words_size_pre)
  **  (CharPtrArray2.missing_i words_pre words_size_pre best_idx row_ptr rows )
  **  (((words_pre + (best_idx * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (best_idx) (rows) ((@nil Z))))) (Znth (best_idx) (rows) ((@nil Z))) )
  **  (IntArray.full ( &( "seen" ) ) 128 seen_l )
) \/
(
forall (words_size_pre: Z) (rows: (@list (@list Z))) (seen_l_2: (@list Z)) (unique: Z) (maxu: Z) (best_idx: Z) (i: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (0 <= (Zlength ((Znth best_idx rows __default__List_Z))))) (PreH2 : (i >= words_size_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= words_size_pre)) (PreH5 : (0 < words_size_pre)) (PreH6 : (words_size_pre <= 100)) (PreH7 : (0 <= best_idx)) (PreH8 : (best_idx < words_size_pre)) (PreH9 : (0 <= maxu)) (PreH10 : (maxu <= 128)) (PreH11 : (0 <= unique)) (PreH12 : (unique <= 128)) (PreH13 : (rows_well_formed_158 rows words_size_pre )) (PreH14 : (problem_158_pre_z rows )) (PreH15 : (best_prefix_state_158 rows i best_idx maxu )) (PreH16 : ((Zlength (seen_l_2)) = 128)) ,
  (CharArray.full row_ptr_2 (Zlength ((Znth best_idx rows __default__List_Z))) (Znth best_idx rows __default__List_Z) )
|--
  “ (problem_158_spec_z rows best_idx ) ” 
  &&  “ (best_prefix_state_158 rows words_size_pre best_idx maxu ) ”
  &&  (CharArray.full row_ptr_2 (Zlength ((Znth (best_idx) (rows) ((@nil Z))))) (Znth (best_idx) (rows) ((@nil Z))) )
).

Definition find_max_entail_wit_17_split_goal_1 := 
forall (words_size_pre: Z) (rows: (@list (@list Z))) (seen_l_2: (@list Z)) (unique: Z) (maxu: Z) (best_idx: Z) (i: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (0 <= (Zlength ((Znth best_idx rows __default__List_Z))))) (PreH2 : (i >= words_size_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= words_size_pre)) (PreH5 : (0 < words_size_pre)) (PreH6 : (words_size_pre <= 100)) (PreH7 : (0 <= best_idx)) (PreH8 : (best_idx < words_size_pre)) (PreH9 : (0 <= maxu)) (PreH10 : (maxu <= 128)) (PreH11 : (0 <= unique)) (PreH12 : (unique <= 128)) (PreH13 : (rows_well_formed_158 rows words_size_pre )) (PreH14 : (problem_158_pre_z rows )) (PreH15 : (best_prefix_state_158 rows i best_idx maxu )) (PreH16 : ((Zlength (seen_l_2)) = 128)) ,
  (CharArray.full row_ptr_2 (Zlength ((Znth best_idx rows __default__List_Z))) (Znth best_idx rows __default__List_Z) )
|--
  “ (problem_158_spec_z rows best_idx ) ”
.

Definition find_max_entail_wit_17_split_goal_2 := 
forall (words_size_pre: Z) (rows: (@list (@list Z))) (seen_l_2: (@list Z)) (unique: Z) (maxu: Z) (best_idx: Z) (i: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (0 <= (Zlength ((Znth best_idx rows __default__List_Z))))) (PreH2 : (i >= words_size_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= words_size_pre)) (PreH5 : (0 < words_size_pre)) (PreH6 : (words_size_pre <= 100)) (PreH7 : (0 <= best_idx)) (PreH8 : (best_idx < words_size_pre)) (PreH9 : (0 <= maxu)) (PreH10 : (maxu <= 128)) (PreH11 : (0 <= unique)) (PreH12 : (unique <= 128)) (PreH13 : (rows_well_formed_158 rows words_size_pre )) (PreH14 : (problem_158_pre_z rows )) (PreH15 : (best_prefix_state_158 rows i best_idx maxu )) (PreH16 : ((Zlength (seen_l_2)) = 128)) ,
  (CharArray.full row_ptr_2 (Zlength ((Znth best_idx rows __default__List_Z))) (Znth best_idx rows __default__List_Z) )
|--
  “ (best_prefix_state_158 rows words_size_pre best_idx maxu ) ”
.

Definition find_max_entail_wit_17_split_goal_spatial := 
forall (words_size_pre: Z) (rows: (@list (@list Z))) (seen_l_2: (@list Z)) (unique: Z) (maxu: Z) (best_idx: Z) (i: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (0 <= (Zlength ((Znth best_idx rows __default__List_Z))))) (PreH2 : (i >= words_size_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= words_size_pre)) (PreH5 : (0 < words_size_pre)) (PreH6 : (words_size_pre <= 100)) (PreH7 : (0 <= best_idx)) (PreH8 : (best_idx < words_size_pre)) (PreH9 : (0 <= maxu)) (PreH10 : (maxu <= 128)) (PreH11 : (0 <= unique)) (PreH12 : (unique <= 128)) (PreH13 : (rows_well_formed_158 rows words_size_pre )) (PreH14 : (problem_158_pre_z rows )) (PreH15 : (best_prefix_state_158 rows i best_idx maxu )) (PreH16 : ((Zlength (seen_l_2)) = 128)) ,
  (CharArray.full row_ptr_2 (Zlength ((Znth best_idx rows __default__List_Z))) (Znth best_idx rows __default__List_Z) )
|--
  (CharArray.full row_ptr_2 (Zlength ((Znth (best_idx) (rows) ((@nil Z))))) (Znth (best_idx) (rows) ((@nil Z))) )
.

Definition find_max_entail_wit_18 := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (seen_l_2: (@list Z)) (best_idx: Z) (maxu: Z) (unique: Z) (PreH1 : (0 <= best_idx)) (PreH2 : (best_idx < words_size_pre)) (PreH3 : (0 <= maxu)) (PreH4 : (maxu <= 128)) (PreH5 : (0 <= unique)) (PreH6 : (unique <= 128)) (PreH7 : (rows_well_formed_158 rows words_size_pre )) (PreH8 : (problem_158_pre_z rows )) (PreH9 : (best_prefix_state_158 rows words_size_pre best_idx maxu )) (PreH10 : (problem_158_spec_z rows best_idx )) (PreH11 : ((Zlength (seen_l_2)) = 128)) ,
  (CharPtrArray2.missing_i words_pre words_size_pre best_idx row_ptr rows )
  **  (((words_pre + (best_idx * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (best_idx) (rows) ((@nil Z))))) (Znth (best_idx) (rows) ((@nil Z))) )
  **  (IntArray.full ( &( "seen" ) ) 128 seen_l_2 )
|--
  EX (seen_l: (@list Z)) ,
  “ (0 <= best_idx) ” 
  &&  “ (best_idx < words_size_pre) ” 
  &&  “ (0 <= maxu) ” 
  &&  “ (maxu <= 128) ” 
  &&  “ (0 <= unique) ” 
  &&  “ (unique <= 128) ” 
  &&  “ (rows_well_formed_158 rows words_size_pre ) ” 
  &&  “ (problem_158_pre_z rows ) ” 
  &&  “ (best_prefix_state_158 rows words_size_pre best_idx maxu ) ” 
  &&  “ (problem_158_spec_z rows best_idx ) ” 
  &&  “ ((Zlength (seen_l)) = 128) ”
  &&  (CharPtrArray2.missing_i words_pre words_size_pre best_idx row_ptr rows )
  **  (((words_pre + (best_idx * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (best_idx) (rows) ((@nil Z))))) (Znth (best_idx) (rows) ((@nil Z))) )
  **  (IntArray.full ( &( "seen" ) ) 128 seen_l )
.

Definition find_max_return_wit_1 := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (row_ptr_2: Z) (seen_l: (@list Z)) (best_idx_2: Z) (maxu: Z) (unique: Z) (PreH1 : (0 <= best_idx_2)) (PreH2 : (best_idx_2 < words_size_pre)) (PreH3 : (0 <= maxu)) (PreH4 : (maxu <= 128)) (PreH5 : (0 <= unique)) (PreH6 : (unique <= 128)) (PreH7 : (rows_well_formed_158 rows words_size_pre )) (PreH8 : (problem_158_pre_z rows )) (PreH9 : (best_prefix_state_158 rows words_size_pre best_idx_2 maxu )) (PreH10 : (problem_158_spec_z rows best_idx_2 )) (PreH11 : ((Zlength (seen_l)) = 128)) ,
  (CharPtrArray2.missing_i words_pre words_size_pre best_idx_2 row_ptr_2 rows )
  **  (((words_pre + (best_idx_2 * sizeof(PTR) ) )) # Ptr  |-> row_ptr_2)
  **  (CharArray.full row_ptr_2 (Zlength ((Znth (best_idx_2) (rows) ((@nil Z))))) (Znth (best_idx_2) (rows) ((@nil Z))) )
|--
  EX (row_ptr: Z)  (best_idx: Z) ,
  “ (0 <= best_idx) ” 
  &&  “ (best_idx < words_size_pre) ” 
  &&  “ (row_ptr_2 = row_ptr) ” 
  &&  “ (problem_158_spec_z rows best_idx ) ”
  &&  (CharPtrArray2.missing_i words_pre words_size_pre best_idx row_ptr rows )
  **  (((words_pre + (best_idx * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (best_idx) (rows) ((@nil Z))))) (Znth (best_idx) (rows) ((@nil Z))) )
.

Definition find_max_partial_solve_wit_1 := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z)))  __default__List_Z (PreH1 : (0 < words_size_pre)) (PreH2 : (words_size_pre <= 100)) (PreH3 : (rows_well_formed_158 rows words_size_pre )) (PreH4 : (problem_158_pre_z rows )) ,
  (IntArray.undef_full ( &( "seen" ) ) 128 )
  **  (CharPtrArray2.full words_pre words_size_pre rows )
|--
  EX (row_ptr: Z) ,
  “ (0 <= (Zlength ((Znth 0 rows __default__List_Z)))) ” 
  &&  “ (0 < words_size_pre) ” 
  &&  “ (words_size_pre <= 100) ” 
  &&  “ (rows_well_formed_158 rows words_size_pre ) ” 
  &&  “ (problem_158_pre_z rows ) ”
  &&  (((words_pre + (0 * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth 0 rows __default__List_Z))) (Znth 0 rows __default__List_Z) )
  **  (CharPtrArray2.missing_i words_pre words_size_pre 0 row_ptr rows )
  **  (IntArray.undef_full ( &( "seen" ) ) 128 )
.

Definition find_max_partial_solve_wit_2 := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (best_idx: Z) (unique: Z) (maxu: Z) (ch: Z) (len: Z) (j: Z) (k: Z) (PreH1 : (k < 128)) (PreH2 : (0 <= k)) (PreH3 : (k <= 128)) (PreH4 : (j = 0)) (PreH5 : (len = 0)) (PreH6 : (ch = 0)) (PreH7 : (maxu = 0)) (PreH8 : (unique = 0)) (PreH9 : (best_idx = 0)) (PreH10 : (0 < words_size_pre)) (PreH11 : (words_size_pre <= 100)) (PreH12 : (rows_well_formed_158 rows words_size_pre )) (PreH13 : (problem_158_pre_z rows )) ,
  (CharPtrArray2.full words_pre words_size_pre rows )
  **  (IntArray.seg ( &( "seen" ) ) 0 k (zeros (k)) )
  **  (IntArray.undef_seg ( &( "seen" ) ) k 128 )
|--
  “ (k < 128) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= 128) ” 
  &&  “ (j = 0) ” 
  &&  “ (len = 0) ” 
  &&  “ (ch = 0) ” 
  &&  “ (maxu = 0) ” 
  &&  “ (unique = 0) ” 
  &&  “ (best_idx = 0) ” 
  &&  “ (0 < words_size_pre) ” 
  &&  “ (words_size_pre <= 100) ” 
  &&  “ (rows_well_formed_158 rows words_size_pre ) ” 
  &&  “ (problem_158_pre_z rows ) ”
  &&  (((( &( "seen" ) ) + (k * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg ( &( "seen" ) ) (k + 1 ) 128 )
  **  (CharPtrArray2.full words_pre words_size_pre rows )
  **  (IntArray.seg ( &( "seen" ) ) 0 k (zeros (k)) )
.

Definition find_max_partial_solve_wit_3 := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (seen_l: (@list Z)) (unique: Z) (maxu: Z) (best_idx: Z) (i: Z) (k: Z) (PreH1 : (k < 128)) (PreH2 : (0 <= k)) (PreH3 : (k <= 128)) (PreH4 : (0 <= i)) (PreH5 : (i < words_size_pre)) (PreH6 : (0 < words_size_pre)) (PreH7 : (words_size_pre <= 100)) (PreH8 : (0 <= best_idx)) (PreH9 : (best_idx < words_size_pre)) (PreH10 : (0 <= maxu)) (PreH11 : (maxu <= 128)) (PreH12 : (0 <= unique)) (PreH13 : (unique <= 128)) (PreH14 : (rows_well_formed_158 rows words_size_pre )) (PreH15 : (problem_158_pre_z rows )) (PreH16 : (best_prefix_state_158 rows i best_idx maxu )) (PreH17 : ((Zlength (seen_l)) = 128)) (PreH18 : (reset_prefix_state_158 k seen_l )) ,
  (CharPtrArray2.missing_i words_pre words_size_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
  **  (IntArray.full ( &( "seen" ) ) 128 seen_l )
|--
  “ (0 <= (Zlength ((Znth (i) (rows) ((@nil Z)))))) ” 
  &&  “ (k < 128) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= 128) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < words_size_pre) ” 
  &&  “ (0 < words_size_pre) ” 
  &&  “ (words_size_pre <= 100) ” 
  &&  “ (0 <= best_idx) ” 
  &&  “ (best_idx < words_size_pre) ” 
  &&  “ (0 <= maxu) ” 
  &&  “ (maxu <= 128) ” 
  &&  “ (0 <= unique) ” 
  &&  “ (unique <= 128) ” 
  &&  “ (rows_well_formed_158 rows words_size_pre ) ” 
  &&  “ (problem_158_pre_z rows ) ” 
  &&  “ (best_prefix_state_158 rows i best_idx maxu ) ” 
  &&  “ ((Zlength (seen_l)) = 128) ” 
  &&  “ (reset_prefix_state_158 k seen_l ) ”
  &&  (((( &( "seen" ) ) + (k * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i ( &( "seen" ) ) k 0 128 seen_l )
  **  (CharPtrArray2.missing_i words_pre words_size_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
.

Definition find_max_partial_solve_wit_4_pure := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (i: Z) (max: Z) (k: Z) (j: Z) (cmp: Z) (len: Z) (ch: Z) (best_idx: Z) (maxu: Z) (unique: Z) (PreH1 : (0 <= i)) (PreH2 : (i < words_size_pre)) (PreH3 : (0 < words_size_pre)) (PreH4 : (words_size_pre <= 100)) (PreH5 : (0 <= best_idx)) (PreH6 : (best_idx < words_size_pre)) (PreH7 : (0 <= maxu)) (PreH8 : (maxu <= 128)) (PreH9 : (0 <= unique)) (PreH10 : (unique <= 128)) (PreH11 : (rows_well_formed_158 rows words_size_pre )) (PreH12 : (problem_158_pre_z rows )) (PreH13 : (best_prefix_state_158 rows i best_idx maxu )) (PreH14 : (valid_string (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) )) (PreH15 : ((string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX)) (PreH16 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = ((string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "words_size" ) )) # Int  |-> words_size_pre)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "max" ) )) # Ptr  |-> max)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "best_idx" ) )) # Int  |-> best_idx)
  **  ((( &( "maxu" ) )) # Int  |-> maxu)
  **  ((( &( "unique" ) )) # Int  |-> unique)
  **  (CharPtrArray2.missing_i words_pre words_size_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) )
  **  (IntArray.full ( &( "seen" ) ) 128 (zeros (128)) )
|--
  “ (valid_string (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) ) ” 
  &&  “ ((string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX) ”
.

Definition find_max_partial_solve_wit_4_aux := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (i: Z) (best_idx: Z) (maxu: Z) (unique: Z) (PreH1 : (0 <= i)) (PreH2 : (i < words_size_pre)) (PreH3 : (0 < words_size_pre)) (PreH4 : (words_size_pre <= 100)) (PreH5 : (0 <= best_idx)) (PreH6 : (best_idx < words_size_pre)) (PreH7 : (0 <= maxu)) (PreH8 : (maxu <= 128)) (PreH9 : (0 <= unique)) (PreH10 : (unique <= 128)) (PreH11 : (rows_well_formed_158 rows words_size_pre )) (PreH12 : (problem_158_pre_z rows )) (PreH13 : (best_prefix_state_158 rows i best_idx maxu )) (PreH14 : (valid_string (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) )) (PreH15 : ((string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX)) (PreH16 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = ((string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) ,
  (CharPtrArray2.missing_i words_pre words_size_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) )
  **  (IntArray.full ( &( "seen" ) ) 128 (zeros (128)) )
|--
  “ (valid_string (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) ) ” 
  &&  “ ((string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX) ” 
  &&  “ (0 <= ((string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < words_size_pre) ” 
  &&  “ (0 < words_size_pre) ” 
  &&  “ (words_size_pre <= 100) ” 
  &&  “ (0 <= best_idx) ” 
  &&  “ (best_idx < words_size_pre) ” 
  &&  “ (0 <= maxu) ” 
  &&  “ (maxu <= 128) ” 
  &&  “ (0 <= unique) ” 
  &&  “ (unique <= 128) ” 
  &&  “ (rows_well_formed_158 rows words_size_pre ) ” 
  &&  “ (problem_158_pre_z rows ) ” 
  &&  “ (best_prefix_state_158 rows i best_idx maxu ) ” 
  &&  “ (valid_string (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) ) ” 
  &&  “ ((string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX) ” 
  &&  “ ((Zlength ((Znth (i) (rows) ((@nil Z))))) = ((string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) + 1 )) ”
  &&  (store_string row_ptr (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) )
  **  (CharPtrArray2.missing_i words_pre words_size_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full ( &( "seen" ) ) 128 (zeros (128)) )
.

Definition find_max_partial_solve_wit_4 := find_max_partial_solve_wit_4_pure -> find_max_partial_solve_wit_4_aux.

Definition find_max_partial_solve_wit_5 := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (seen_l: (@list Z)) (ch: Z) (unique: Z) (maxu: Z) (best_idx: Z) (row_ptr: Z) (i: Z) (len: Z) (j: Z) (PreH1 : (j < len)) (PreH2 : (0 <= j)) (PreH3 : (j <= len)) (PreH4 : (0 <= i)) (PreH5 : (i < words_size_pre)) (PreH6 : (0 < words_size_pre)) (PreH7 : (words_size_pre <= 100)) (PreH8 : (0 <= best_idx)) (PreH9 : (best_idx < words_size_pre)) (PreH10 : (0 <= maxu)) (PreH11 : (maxu <= 128)) (PreH12 : (0 <= unique)) (PreH13 : (unique <= 128)) (PreH14 : (len = (string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))))) (PreH15 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = (len + 1 ))) (PreH16 : (valid_string (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) )) (PreH17 : (0 <= ch)) (PreH18 : (ch <= 127)) (PreH19 : ((Zlength (seen_l)) = 128)) (PreH20 : (rows_well_formed_158 rows words_size_pre )) (PreH21 : (problem_158_pre_z rows )) (PreH22 : (best_prefix_state_158 rows i best_idx maxu )) (PreH23 : (count_scan_state_158 (Znth (i) (rows) ((@nil Z))) j seen_l unique )) ,
  (CharPtrArray2.missing_i words_pre words_size_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
  **  (IntArray.full ( &( "seen" ) ) 128 seen_l )
|--
  “ (j < len) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= len) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < words_size_pre) ” 
  &&  “ (0 < words_size_pre) ” 
  &&  “ (words_size_pre <= 100) ” 
  &&  “ (0 <= best_idx) ” 
  &&  “ (best_idx < words_size_pre) ” 
  &&  “ (0 <= maxu) ” 
  &&  “ (maxu <= 128) ” 
  &&  “ (0 <= unique) ” 
  &&  “ (unique <= 128) ” 
  &&  “ (len = (string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z)))))))) ” 
  &&  “ ((Zlength ((Znth (i) (rows) ((@nil Z))))) = (len + 1 )) ” 
  &&  “ (valid_string (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) ) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ ((Zlength (seen_l)) = 128) ” 
  &&  “ (rows_well_formed_158 rows words_size_pre ) ” 
  &&  “ (problem_158_pre_z rows ) ” 
  &&  “ (best_prefix_state_158 rows i best_idx maxu ) ” 
  &&  “ (count_scan_state_158 (Znth (i) (rows) ((@nil Z))) j seen_l unique ) ”
  &&  (((row_ptr + (j * sizeof(CHAR) ) )) # Char  |-> (Znth j (Znth (i) (rows) ((@nil Z))) 0))
  **  (CharArray.missing_i row_ptr j 0 (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
  **  (CharPtrArray2.missing_i words_pre words_size_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full ( &( "seen" ) ) 128 seen_l )
.

Definition find_max_partial_solve_wit_6 := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (seen_l: (@list Z)) (j: Z) (len: Z) (i: Z) (ch: Z) (best_idx: Z) (maxu: Z) (unique: Z) (PreH1 : (0 <= j)) (PreH2 : (j < len)) (PreH3 : (0 <= i)) (PreH4 : (i < words_size_pre)) (PreH5 : (0 < words_size_pre)) (PreH6 : (words_size_pre <= 100)) (PreH7 : (0 <= ch)) (PreH8 : (ch < 128)) (PreH9 : (ch = (Znth (j) ((Znth (i) (rows) ((@nil Z)))) (0)))) (PreH10 : (0 <= best_idx)) (PreH11 : (best_idx < words_size_pre)) (PreH12 : (0 <= maxu)) (PreH13 : (maxu <= 128)) (PreH14 : (0 <= unique)) (PreH15 : (unique <= 128)) (PreH16 : (len = (string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))))) (PreH17 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = (len + 1 ))) (PreH18 : (valid_string (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) )) (PreH19 : ((Zlength (seen_l)) = 128)) (PreH20 : (rows_well_formed_158 rows words_size_pre )) (PreH21 : (problem_158_pre_z rows )) (PreH22 : (best_prefix_state_158 rows i best_idx maxu )) (PreH23 : (count_scan_state_158 (Znth (i) (rows) ((@nil Z))) j seen_l unique )) ,
  (CharPtrArray2.missing_i words_pre words_size_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
  **  (IntArray.full ( &( "seen" ) ) 128 seen_l )
|--
  “ (0 <= (Zlength ((Znth (i) (rows) ((@nil Z)))))) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < len) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < words_size_pre) ” 
  &&  “ (0 < words_size_pre) ” 
  &&  “ (words_size_pre <= 100) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch < 128) ” 
  &&  “ (ch = (Znth (j) ((Znth (i) (rows) ((@nil Z)))) (0))) ” 
  &&  “ (0 <= best_idx) ” 
  &&  “ (best_idx < words_size_pre) ” 
  &&  “ (0 <= maxu) ” 
  &&  “ (maxu <= 128) ” 
  &&  “ (0 <= unique) ” 
  &&  “ (unique <= 128) ” 
  &&  “ (len = (string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z)))))))) ” 
  &&  “ ((Zlength ((Znth (i) (rows) ((@nil Z))))) = (len + 1 )) ” 
  &&  “ (valid_string (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) ) ” 
  &&  “ ((Zlength (seen_l)) = 128) ” 
  &&  “ (rows_well_formed_158 rows words_size_pre ) ” 
  &&  “ (problem_158_pre_z rows ) ” 
  &&  “ (best_prefix_state_158 rows i best_idx maxu ) ” 
  &&  “ (count_scan_state_158 (Znth (i) (rows) ((@nil Z))) j seen_l unique ) ”
  &&  (((( &( "seen" ) ) + (ch * sizeof(INT) ) )) # Int  |-> (Znth ch seen_l 0))
  **  (IntArray.missing_i ( &( "seen" ) ) ch 0 128 seen_l )
  **  (CharPtrArray2.missing_i words_pre words_size_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
.

Definition find_max_partial_solve_wit_7 := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (seen_l: (@list Z)) (j: Z) (len: Z) (i: Z) (ch: Z) (best_idx: Z) (maxu: Z) (unique: Z) (PreH1 : ((Znth ch seen_l 0) = 0)) (PreH2 : (0 <= (Zlength ((Znth (i) (rows) ((@nil Z))))))) (PreH3 : (0 <= j)) (PreH4 : (j < len)) (PreH5 : (0 <= i)) (PreH6 : (i < words_size_pre)) (PreH7 : (0 < words_size_pre)) (PreH8 : (words_size_pre <= 100)) (PreH9 : (0 <= ch)) (PreH10 : (ch < 128)) (PreH11 : (ch = (Znth (j) ((Znth (i) (rows) ((@nil Z)))) (0)))) (PreH12 : (0 <= best_idx)) (PreH13 : (best_idx < words_size_pre)) (PreH14 : (0 <= maxu)) (PreH15 : (maxu <= 128)) (PreH16 : (0 <= unique)) (PreH17 : (unique <= 128)) (PreH18 : (len = (string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))))) (PreH19 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = (len + 1 ))) (PreH20 : (valid_string (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) )) (PreH21 : ((Zlength (seen_l)) = 128)) (PreH22 : (rows_well_formed_158 rows words_size_pre )) (PreH23 : (problem_158_pre_z rows )) (PreH24 : (best_prefix_state_158 rows i best_idx maxu )) (PreH25 : (count_scan_state_158 (Znth (i) (rows) ((@nil Z))) j seen_l unique )) ,
  (IntArray.full ( &( "seen" ) ) 128 seen_l )
  **  (CharPtrArray2.missing_i words_pre words_size_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
|--
  “ ((Znth ch seen_l 0) = 0) ” 
  &&  “ (0 <= (Zlength ((Znth (i) (rows) ((@nil Z)))))) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < len) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < words_size_pre) ” 
  &&  “ (0 < words_size_pre) ” 
  &&  “ (words_size_pre <= 100) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch < 128) ” 
  &&  “ (ch = (Znth (j) ((Znth (i) (rows) ((@nil Z)))) (0))) ” 
  &&  “ (0 <= best_idx) ” 
  &&  “ (best_idx < words_size_pre) ” 
  &&  “ (0 <= maxu) ” 
  &&  “ (maxu <= 128) ” 
  &&  “ (0 <= unique) ” 
  &&  “ (unique <= 128) ” 
  &&  “ (len = (string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z)))))))) ” 
  &&  “ ((Zlength ((Znth (i) (rows) ((@nil Z))))) = (len + 1 )) ” 
  &&  “ (valid_string (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) ) ” 
  &&  “ ((Zlength (seen_l)) = 128) ” 
  &&  “ (rows_well_formed_158 rows words_size_pre ) ” 
  &&  “ (problem_158_pre_z rows ) ” 
  &&  “ (best_prefix_state_158 rows i best_idx maxu ) ” 
  &&  “ (count_scan_state_158 (Znth (i) (rows) ((@nil Z))) j seen_l unique ) ”
  &&  (((( &( "seen" ) ) + (ch * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i ( &( "seen" ) ) ch 0 128 seen_l )
  **  (CharPtrArray2.missing_i words_pre words_size_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
.

Definition find_max_partial_solve_wit_8_pure := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (best_ptr: Z) (seen_l: (@list Z)) (i: Z) (best_idx: Z) (k: Z) (j: Z) (cmp: Z) (unique: Z) (maxu: Z) (len_addr_v: Z) (ch_addr_v: Z) (PreH1 : (0 <= i)) (PreH2 : (i < words_size_pre)) (PreH3 : (0 < words_size_pre)) (PreH4 : (words_size_pre <= 100)) (PreH5 : (0 <= best_idx)) (PreH6 : (best_idx < words_size_pre)) (PreH7 : (i <> best_idx)) (PreH8 : (unique = (row_unique_count_z_158 ((Znth (i) (rows) ((@nil Z))))))) (PreH9 : (unique = maxu)) (PreH10 : (0 <= maxu)) (PreH11 : (maxu <= 128)) (PreH12 : (0 <= unique)) (PreH13 : (unique <= 128)) (PreH14 : (rows_well_formed_158 rows words_size_pre )) (PreH15 : (problem_158_pre_z rows )) (PreH16 : (best_prefix_state_158 rows i best_idx maxu )) (PreH17 : (valid_string (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) )) (PreH18 : (valid_string (row_payload_z_158 ((Znth (best_idx) (rows) ((@nil Z))))) )) (PreH19 : ((string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX)) (PreH20 : ((string_length ((row_payload_z_158 ((Znth (best_idx) (rows) ((@nil Z))))))) < INT_MAX)) (PreH21 : ((Zlength (seen_l)) = 128)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best_idx" ) )) # Int  |-> best_idx)
  **  ((( &( "words_size" ) )) # Int  |-> words_size_pre)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "max" ) )) # Ptr  |-> best_ptr)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "unique" ) )) # Int  |-> unique)
  **  ((( &( "maxu" ) )) # Int  |-> maxu)
  **  (char_ptr_array2_missing_two_158 words_pre words_size_pre i row_ptr best_idx best_ptr rows )
  **  (store_string row_ptr (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) )
  **  (((words_pre + (best_idx * sizeof(PTR) ) )) # Ptr  |-> best_ptr)
  **  (store_string best_ptr (row_payload_z_158 ((Znth (best_idx) (rows) ((@nil Z))))) )
  **  ((( &( "len" ) )) # Int  |-> len_addr_v)
  **  ((( &( "ch" ) )) # Int  |-> ch_addr_v)
  **  (IntArray.full ( &( "seen" ) ) 128 seen_l )
|--
  “ (valid_string (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) ) ” 
  &&  “ (valid_string (row_payload_z_158 ((Znth (best_idx) (rows) ((@nil Z))))) ) ” 
  &&  “ ((string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX) ” 
  &&  “ ((string_length ((row_payload_z_158 ((Znth (best_idx) (rows) ((@nil Z))))))) < INT_MAX) ”
.

Definition find_max_partial_solve_wit_8_aux := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (best_ptr: Z) (seen_l: (@list Z)) (i: Z) (best_idx: Z) (unique: Z) (maxu: Z) (PreH1 : (0 <= i)) (PreH2 : (i < words_size_pre)) (PreH3 : (0 < words_size_pre)) (PreH4 : (words_size_pre <= 100)) (PreH5 : (0 <= best_idx)) (PreH6 : (best_idx < words_size_pre)) (PreH7 : (i <> best_idx)) (PreH8 : (unique = (row_unique_count_z_158 ((Znth (i) (rows) ((@nil Z))))))) (PreH9 : (unique = maxu)) (PreH10 : (0 <= maxu)) (PreH11 : (maxu <= 128)) (PreH12 : (0 <= unique)) (PreH13 : (unique <= 128)) (PreH14 : (rows_well_formed_158 rows words_size_pre )) (PreH15 : (problem_158_pre_z rows )) (PreH16 : (best_prefix_state_158 rows i best_idx maxu )) (PreH17 : (valid_string (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) )) (PreH18 : (valid_string (row_payload_z_158 ((Znth (best_idx) (rows) ((@nil Z))))) )) (PreH19 : ((string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX)) (PreH20 : ((string_length ((row_payload_z_158 ((Znth (best_idx) (rows) ((@nil Z))))))) < INT_MAX)) (PreH21 : ((Zlength (seen_l)) = 128)) ,
  (char_ptr_array2_missing_two_158 words_pre words_size_pre i row_ptr best_idx best_ptr rows )
  **  (store_string row_ptr (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) )
  **  (((words_pre + (best_idx * sizeof(PTR) ) )) # Ptr  |-> best_ptr)
  **  (store_string best_ptr (row_payload_z_158 ((Znth (best_idx) (rows) ((@nil Z))))) )
  **  (IntArray.full ( &( "seen" ) ) 128 seen_l )
|--
  “ (valid_string (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) ) ” 
  &&  “ (valid_string (row_payload_z_158 ((Znth (best_idx) (rows) ((@nil Z))))) ) ” 
  &&  “ ((string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX) ” 
  &&  “ ((string_length ((row_payload_z_158 ((Znth (best_idx) (rows) ((@nil Z))))))) < INT_MAX) ” 
  &&  “ (0 <= ((string_length ((row_payload_z_158 ((Znth (best_idx) (rows) ((@nil Z))))))) + 1 )) ” 
  &&  “ (0 <= ((string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < words_size_pre) ” 
  &&  “ (0 < words_size_pre) ” 
  &&  “ (words_size_pre <= 100) ” 
  &&  “ (0 <= best_idx) ” 
  &&  “ (best_idx < words_size_pre) ” 
  &&  “ (i <> best_idx) ” 
  &&  “ (unique = (row_unique_count_z_158 ((Znth (i) (rows) ((@nil Z)))))) ” 
  &&  “ (unique = maxu) ” 
  &&  “ (0 <= maxu) ” 
  &&  “ (maxu <= 128) ” 
  &&  “ (0 <= unique) ” 
  &&  “ (unique <= 128) ” 
  &&  “ (rows_well_formed_158 rows words_size_pre ) ” 
  &&  “ (problem_158_pre_z rows ) ” 
  &&  “ (best_prefix_state_158 rows i best_idx maxu ) ” 
  &&  “ (valid_string (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) ) ” 
  &&  “ (valid_string (row_payload_z_158 ((Znth (best_idx) (rows) ((@nil Z))))) ) ” 
  &&  “ ((string_length ((row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX) ” 
  &&  “ ((string_length ((row_payload_z_158 ((Znth (best_idx) (rows) ((@nil Z))))))) < INT_MAX) ” 
  &&  “ ((Zlength (seen_l)) = 128) ”
  &&  (store_string row_ptr (row_payload_z_158 ((Znth (i) (rows) ((@nil Z))))) )
  **  (store_string best_ptr (row_payload_z_158 ((Znth (best_idx) (rows) ((@nil Z))))) )
  **  (char_ptr_array2_missing_two_158 words_pre words_size_pre i row_ptr best_idx best_ptr rows )
  **  (((words_pre + (best_idx * sizeof(PTR) ) )) # Ptr  |-> best_ptr)
  **  (IntArray.full ( &( "seen" ) ) 128 seen_l )
.

Definition find_max_partial_solve_wit_8 := find_max_partial_solve_wit_8_pure -> find_max_partial_solve_wit_8_aux.

Module Type VC_Correct.

Include ptr_array2_Strategy_Correct.
Include char_array_Strategy_Correct.
Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.
Include string_Strategy_Correct.

Axiom proof_of_find_max_safety_wit_1 : find_max_safety_wit_1.
Axiom proof_of_find_max_safety_wit_2 : find_max_safety_wit_2.
Axiom proof_of_find_max_safety_wit_3 : find_max_safety_wit_3.
Axiom proof_of_find_max_safety_wit_4 : find_max_safety_wit_4.
Axiom proof_of_find_max_safety_wit_5 : find_max_safety_wit_5.
Axiom proof_of_find_max_safety_wit_6 : find_max_safety_wit_6.
Axiom proof_of_find_max_safety_wit_7 : find_max_safety_wit_7.
Axiom proof_of_find_max_safety_wit_8 : find_max_safety_wit_8.
Axiom proof_of_find_max_safety_wit_9 : find_max_safety_wit_9.
Axiom proof_of_find_max_safety_wit_10 : find_max_safety_wit_10.
Axiom proof_of_find_max_safety_wit_11 : find_max_safety_wit_11.
Axiom proof_of_find_max_safety_wit_12 : find_max_safety_wit_12.
Axiom proof_of_find_max_safety_wit_13 : find_max_safety_wit_13.
Axiom proof_of_find_max_safety_wit_14 : find_max_safety_wit_14.
Axiom proof_of_find_max_safety_wit_15 : find_max_safety_wit_15.
Axiom proof_of_find_max_safety_wit_16 : find_max_safety_wit_16.
Axiom proof_of_find_max_safety_wit_17 : find_max_safety_wit_17.
Axiom proof_of_find_max_safety_wit_18 : find_max_safety_wit_18.
Axiom proof_of_find_max_safety_wit_19 : find_max_safety_wit_19.
Axiom proof_of_find_max_safety_wit_20 : find_max_safety_wit_20.
Axiom proof_of_find_max_safety_wit_21 : find_max_safety_wit_21.
Axiom proof_of_find_max_safety_wit_22 : find_max_safety_wit_22.
Axiom proof_of_find_max_safety_wit_23 : find_max_safety_wit_23.
Axiom proof_of_find_max_safety_wit_24 : find_max_safety_wit_24.
Axiom proof_of_find_max_safety_wit_25 : find_max_safety_wit_25.
Axiom proof_of_find_max_safety_wit_26 : find_max_safety_wit_26.
Axiom proof_of_find_max_safety_wit_27 : find_max_safety_wit_27.
Axiom proof_of_find_max_safety_wit_28 : find_max_safety_wit_28.
Axiom proof_of_find_max_safety_wit_29 : find_max_safety_wit_29.
Axiom proof_of_find_max_safety_wit_30 : find_max_safety_wit_30.
Axiom proof_of_find_max_safety_wit_31 : find_max_safety_wit_31.
Axiom proof_of_find_max_safety_wit_32 : find_max_safety_wit_32.
Axiom proof_of_find_max_safety_wit_33 : find_max_safety_wit_33.
Axiom proof_of_find_max_safety_wit_34 : find_max_safety_wit_34.
Axiom proof_of_find_max_safety_wit_35 : find_max_safety_wit_35.
Axiom proof_of_find_max_entail_wit_1 : find_max_entail_wit_1.
Axiom proof_of_find_max_entail_wit_2 : find_max_entail_wit_2.
Axiom proof_of_find_max_entail_wit_3 : find_max_entail_wit_3.
Axiom proof_of_find_max_entail_wit_4 : find_max_entail_wit_4.
Axiom proof_of_find_max_entail_wit_5 : find_max_entail_wit_5.
Axiom proof_of_find_max_entail_wit_6 : find_max_entail_wit_6.
Axiom proof_of_find_max_entail_wit_7 : find_max_entail_wit_7.
Axiom proof_of_find_max_entail_wit_8 : find_max_entail_wit_8.
Axiom proof_of_find_max_entail_wit_9 : find_max_entail_wit_9.
Axiom proof_of_find_max_entail_wit_10 : find_max_entail_wit_10.
Axiom proof_of_find_max_entail_wit_11_1 : find_max_entail_wit_11_1.
Axiom proof_of_find_max_entail_wit_11_2 : find_max_entail_wit_11_2.
Axiom proof_of_find_max_entail_wit_12 : find_max_entail_wit_12.
Axiom proof_of_find_max_entail_wit_13 : find_max_entail_wit_13.
Axiom proof_of_find_max_entail_wit_14 : find_max_entail_wit_14.
Axiom proof_of_find_max_entail_wit_15_1 : find_max_entail_wit_15_1.
Axiom proof_of_find_max_entail_wit_15_2 : find_max_entail_wit_15_2.
Axiom proof_of_find_max_entail_wit_15_3 : find_max_entail_wit_15_3.
Axiom proof_of_find_max_entail_wit_15_4 : find_max_entail_wit_15_4.
Axiom proof_of_find_max_entail_wit_15_5 : find_max_entail_wit_15_5.
Axiom proof_of_find_max_entail_wit_16 : find_max_entail_wit_16.
Axiom proof_of_find_max_entail_wit_17 : find_max_entail_wit_17.
Axiom proof_of_find_max_entail_wit_18 : find_max_entail_wit_18.
Axiom proof_of_find_max_return_wit_1 : find_max_return_wit_1.
Axiom proof_of_find_max_partial_solve_wit_1 : find_max_partial_solve_wit_1.
Axiom proof_of_find_max_partial_solve_wit_2 : find_max_partial_solve_wit_2.
Axiom proof_of_find_max_partial_solve_wit_3 : find_max_partial_solve_wit_3.
Axiom proof_of_find_max_partial_solve_wit_4_pure : find_max_partial_solve_wit_4_pure.
Axiom proof_of_find_max_partial_solve_wit_4 : find_max_partial_solve_wit_4.
Axiom proof_of_find_max_partial_solve_wit_5 : find_max_partial_solve_wit_5.
Axiom proof_of_find_max_partial_solve_wit_6 : find_max_partial_solve_wit_6.
Axiom proof_of_find_max_partial_solve_wit_7 : find_max_partial_solve_wit_7.
Axiom proof_of_find_max_partial_solve_wit_8_pure : find_max_partial_solve_wit_8_pure.
Axiom proof_of_find_max_partial_solve_wit_8 : find_max_partial_solve_wit_8.

End VC_Correct.
