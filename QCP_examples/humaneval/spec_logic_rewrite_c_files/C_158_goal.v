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
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (PreH1 : (0 < words_size_pre)) (PreH2 : (words_size_pre < INT_MAX)) (PreH3 : ((Zlength (ptrs)) = words_size_pre)) (PreH4 : (rows_well_formed_158 rows words_size_pre )) (PreH5 : (problem_158_pre_z rows )) ,
  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "words_size" ) )) # Int  |-> words_size_pre)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  (PtrArray.full words_pre words_size_pre ptrs )
  **  (row_stores_158 ptrs rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition find_max_safety_wit_2 := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (PreH1 : (0 < words_size_pre)) (PreH2 : (words_size_pre < INT_MAX)) (PreH3 : ((Zlength (ptrs)) = words_size_pre)) (PreH4 : (rows_well_formed_158 rows words_size_pre )) (PreH5 : (problem_158_pre_z rows )) ,
  ((( &( "max" ) )) # Ptr  |->_)
  **  ((( &( "best" ) )) # Int  |-> 0)
  **  ((( &( "words_size" ) )) # Int  |-> words_size_pre)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  (PtrArray.full words_pre words_size_pre ptrs )
  **  (row_stores_158 ptrs rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition find_max_safety_wit_3 := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (PreH1 : (0 < words_size_pre)) (PreH2 : (words_size_pre < INT_MAX)) (PreH3 : ((Zlength (ptrs)) = words_size_pre)) (PreH4 : (rows_well_formed_158 rows words_size_pre )) (PreH5 : (problem_158_pre_z rows )) ,
  ((( &( "maxu" ) )) # Int  |->_)
  **  (PtrArray.full words_pre words_size_pre ptrs )
  **  ((( &( "max" ) )) # Ptr  |-> (Znth 0 ptrs 0))
  **  ((( &( "best" ) )) # Int  |-> 0)
  **  ((( &( "words_size" ) )) # Int  |-> words_size_pre)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  (row_stores_158 ptrs rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition find_max_safety_wit_4 := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (PreH1 : (0 < words_size_pre)) (PreH2 : (words_size_pre < INT_MAX)) (PreH3 : ((Zlength (ptrs)) = words_size_pre)) (PreH4 : (rows_well_formed_158 rows words_size_pre )) (PreH5 : (problem_158_pre_z rows )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "maxu" ) )) # Int  |-> 0)
  **  (PtrArray.full words_pre words_size_pre ptrs )
  **  ((( &( "max" ) )) # Ptr  |-> (Znth 0 ptrs 0))
  **  ((( &( "best" ) )) # Int  |-> 0)
  **  ((( &( "words_size" ) )) # Int  |-> words_size_pre)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  (row_stores_158 ptrs rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition find_max_safety_wit_5 := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (maxu: Z) (max: Z) (best: Z) (i: Z) (PreH1 : (i < words_size_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= words_size_pre)) (PreH4 : (0 < words_size_pre)) (PreH5 : (words_size_pre < INT_MAX)) (PreH6 : ((Zlength (ptrs)) = words_size_pre)) (PreH7 : (rows_well_formed_158 rows words_size_pre )) (PreH8 : (problem_158_pre_z rows )) (PreH9 : (0 <= best)) (PreH10 : (best < words_size_pre)) (PreH11 : (max = (Znth (best) (ptrs) (0)))) (PreH12 : (best_state_158 rows i best maxu )) ,
  ((( &( "k" ) )) # Int  |->_)
  **  (IntArray.undef_full ( &( "seen" ) ) 256 )
  **  (PtrArray.full words_pre words_size_pre ptrs )
  **  ((( &( "cur" ) )) # Ptr  |-> (Znth i ptrs 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "words_size" ) )) # Int  |-> words_size_pre)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "max" ) )) # Ptr  |-> max)
  **  ((( &( "maxu" ) )) # Int  |-> maxu)
  **  (row_stores_158 ptrs rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition find_max_safety_wit_6 := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (maxu: Z) (best: Z) (max: Z) (cur: Z) (i: Z) (zeros: (@list Z)) (k: Z) (PreH1 : (0 <= k)) (PreH2 : (k <= 256)) (PreH3 : (zeros = (repeat_Z (0) (k)))) (PreH4 : (0 <= i)) (PreH5 : (i < words_size_pre)) (PreH6 : (cur = (Znth (i) (ptrs) (0)))) (PreH7 : (max = (Znth (best) (ptrs) (0)))) (PreH8 : (0 < words_size_pre)) (PreH9 : (words_size_pre < INT_MAX)) (PreH10 : (0 <= best)) (PreH11 : (best < words_size_pre)) (PreH12 : ((Zlength (ptrs)) = words_size_pre)) (PreH13 : (rows_well_formed_158 rows words_size_pre )) (PreH14 : (problem_158_pre_z rows )) (PreH15 : (best_state_158 rows i best maxu )) ,
  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "words_size" ) )) # Int  |-> words_size_pre)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "max" ) )) # Ptr  |-> max)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "maxu" ) )) # Int  |-> maxu)
  **  (PtrArray.full words_pre words_size_pre ptrs )
  **  (row_stores_158 ptrs rows )
  **  (IntArray.seg ( &( "seen" ) ) 0 k zeros )
  **  (IntArray.undef_seg ( &( "seen" ) ) k 256 )
|--
  “ (256 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 256) ”
.

Definition find_max_safety_wit_7 := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (maxu: Z) (best: Z) (max: Z) (cur: Z) (i: Z) (zeros: (@list Z)) (k: Z) (PreH1 : (k < 256)) (PreH2 : (0 <= k)) (PreH3 : (k <= 256)) (PreH4 : (zeros = (repeat_Z (0) (k)))) (PreH5 : (0 <= i)) (PreH6 : (i < words_size_pre)) (PreH7 : (cur = (Znth (i) (ptrs) (0)))) (PreH8 : (max = (Znth (best) (ptrs) (0)))) (PreH9 : (0 < words_size_pre)) (PreH10 : (words_size_pre < INT_MAX)) (PreH11 : (0 <= best)) (PreH12 : (best < words_size_pre)) (PreH13 : ((Zlength (ptrs)) = words_size_pre)) (PreH14 : (rows_well_formed_158 rows words_size_pre )) (PreH15 : (problem_158_pre_z rows )) (PreH16 : (best_state_158 rows i best maxu )) ,
  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "words_size" ) )) # Int  |-> words_size_pre)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "max" ) )) # Ptr  |-> max)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "maxu" ) )) # Int  |-> maxu)
  **  (PtrArray.full words_pre words_size_pre ptrs )
  **  (row_stores_158 ptrs rows )
  **  (IntArray.seg ( &( "seen" ) ) 0 k zeros )
  **  (IntArray.undef_seg ( &( "seen" ) ) k 256 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition find_max_safety_wit_8 := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (maxu: Z) (best: Z) (max: Z) (cur: Z) (i: Z) (zeros: (@list Z)) (k: Z) (PreH1 : (k < 256)) (PreH2 : (0 <= k)) (PreH3 : (k <= 256)) (PreH4 : (zeros = (repeat_Z (0) (k)))) (PreH5 : (0 <= i)) (PreH6 : (i < words_size_pre)) (PreH7 : (cur = (Znth (i) (ptrs) (0)))) (PreH8 : (max = (Znth (best) (ptrs) (0)))) (PreH9 : (0 < words_size_pre)) (PreH10 : (words_size_pre < INT_MAX)) (PreH11 : (0 <= best)) (PreH12 : (best < words_size_pre)) (PreH13 : ((Zlength (ptrs)) = words_size_pre)) (PreH14 : (rows_well_formed_158 rows words_size_pre )) (PreH15 : (problem_158_pre_z rows )) (PreH16 : (best_state_158 rows i best maxu )) ,
  (IntArray.seg ( &( "seen" ) ) 0 (k + 1 ) (app (zeros) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "seen" ) ) (k + 1 ) 256 )
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "words_size" ) )) # Int  |-> words_size_pre)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "max" ) )) # Ptr  |-> max)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "maxu" ) )) # Int  |-> maxu)
  **  (PtrArray.full words_pre words_size_pre ptrs )
  **  (row_stores_158 ptrs rows )
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition find_max_safety_wit_9 := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (i: Z) (k: Z) (cur: Z) (max: Z) (best: Z) (maxu: Z) (retval: Z) (PreH1 : (retval = (string_length ((Znth (i) (rows) ((@nil Z))))))) (PreH2 : (0 <= ((string_length ((Znth (i) (rows) ((@nil Z))))) + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < words_size_pre)) (PreH5 : (k = 256)) (PreH6 : (cur = (Znth (i) (ptrs) (0)))) (PreH7 : (max = (Znth (best) (ptrs) (0)))) (PreH8 : (0 < words_size_pre)) (PreH9 : (words_size_pre < INT_MAX)) (PreH10 : ((Zlength (ptrs)) = words_size_pre)) (PreH11 : (problem_158_pre_z rows )) (PreH12 : (rows_well_formed_158 rows words_size_pre )) (PreH13 : (best_state_158 rows i best maxu )) ,
  ((( &( "unique" ) )) # Int  |->_)
  **  (store_string cur (Znth (i) (rows) ((@nil Z))) )
  **  ((( &( "len" ) )) # Int  |-> retval)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "words_size" ) )) # Int  |-> words_size_pre)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "max" ) )) # Ptr  |-> max)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "maxu" ) )) # Int  |-> maxu)
  **  (PtrArray.full words_pre words_size_pre ptrs )
  **  (row_stores_missing_i_158 ptrs rows i )
  **  (IntArray.full ( &( "seen" ) ) 256 (repeat_Z (0) (256)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition find_max_safety_wit_10 := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (i: Z) (k: Z) (cur: Z) (max: Z) (best: Z) (maxu: Z) (retval: Z) (PreH1 : (retval = (string_length ((Znth (i) (rows) ((@nil Z))))))) (PreH2 : (0 <= ((string_length ((Znth (i) (rows) ((@nil Z))))) + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < words_size_pre)) (PreH5 : (k = 256)) (PreH6 : (cur = (Znth (i) (ptrs) (0)))) (PreH7 : (max = (Znth (best) (ptrs) (0)))) (PreH8 : (0 < words_size_pre)) (PreH9 : (words_size_pre < INT_MAX)) (PreH10 : ((Zlength (ptrs)) = words_size_pre)) (PreH11 : (problem_158_pre_z rows )) (PreH12 : (rows_well_formed_158 rows words_size_pre )) (PreH13 : (best_state_158 rows i best maxu )) ,
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "unique" ) )) # Int  |-> 0)
  **  (store_string cur (Znth (i) (rows) ((@nil Z))) )
  **  ((( &( "len" ) )) # Int  |-> retval)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "words_size" ) )) # Int  |-> words_size_pre)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "max" ) )) # Ptr  |-> max)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "maxu" ) )) # Int  |-> maxu)
  **  (PtrArray.full words_pre words_size_pre ptrs )
  **  (row_stores_missing_i_158 ptrs rows i )
  **  (IntArray.full ( &( "seen" ) ) 256 (repeat_Z (0) (256)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition find_max_safety_wit_11 := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (seen_l: (@list Z)) (j: Z) (len: Z) (i: Z) (unique: Z) (ch: Z) (k: Z) (cur: Z) (max: Z) (best: Z) (maxu: Z) (PreH1 : (0 <= ((string_length ((Znth (i) (rows) ((@nil Z))))) + 1 ))) (PreH2 : (0 <= j)) (PreH3 : (j < len)) (PreH4 : (len = (string_length ((Znth (i) (rows) ((@nil Z))))))) (PreH5 : (0 <= unique)) (PreH6 : (unique <= j)) (PreH7 : (0 <= ch)) (PreH8 : (ch < 256)) (PreH9 : (ch = (Znth (j) ((Znth (i) (rows) ((@nil Z)))) (0)))) (PreH10 : (k = 256)) (PreH11 : (0 <= i)) (PreH12 : (i < words_size_pre)) (PreH13 : (cur = (Znth (i) (ptrs) (0)))) (PreH14 : (max = (Znth (best) (ptrs) (0)))) (PreH15 : (0 <= best)) (PreH16 : (best < words_size_pre)) (PreH17 : (0 < words_size_pre)) (PreH18 : (words_size_pre < INT_MAX)) (PreH19 : ((Zlength (ptrs)) = words_size_pre)) (PreH20 : (problem_158_pre_z rows )) (PreH21 : (rows_well_formed_158 rows words_size_pre )) (PreH22 : (best_state_158 rows i best maxu )) (PreH23 : (seen_state_158 (Znth (i) (rows) ((@nil Z))) j seen_l unique )) ,
  (IntArray.full ( &( "seen" ) ) 256 seen_l )
  **  (CharArray.full cur ((string_length ((Znth (i) (rows) ((@nil Z))))) + 1 ) (c_string ((Znth (i) (rows) ((@nil Z))))) )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "unique" ) )) # Int  |-> unique)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "words_size" ) )) # Int  |-> words_size_pre)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "max" ) )) # Ptr  |-> max)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "maxu" ) )) # Int  |-> maxu)
  **  (PtrArray.full words_pre words_size_pre ptrs )
  **  (row_stores_missing_i_158 ptrs rows i )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition find_max_safety_wit_12 := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (seen_l: (@list Z)) (j: Z) (len: Z) (i: Z) (unique: Z) (ch: Z) (k: Z) (cur: Z) (max: Z) (best: Z) (maxu: Z) (PreH1 : ((Znth ch seen_l 0) = 0)) (PreH2 : (0 <= ((string_length ((Znth (i) (rows) ((@nil Z))))) + 1 ))) (PreH3 : (0 <= j)) (PreH4 : (j < len)) (PreH5 : (len = (string_length ((Znth (i) (rows) ((@nil Z))))))) (PreH6 : (0 <= unique)) (PreH7 : (unique <= j)) (PreH8 : (0 <= ch)) (PreH9 : (ch < 256)) (PreH10 : (ch = (Znth (j) ((Znth (i) (rows) ((@nil Z)))) (0)))) (PreH11 : (k = 256)) (PreH12 : (0 <= i)) (PreH13 : (i < words_size_pre)) (PreH14 : (cur = (Znth (i) (ptrs) (0)))) (PreH15 : (max = (Znth (best) (ptrs) (0)))) (PreH16 : (0 <= best)) (PreH17 : (best < words_size_pre)) (PreH18 : (0 < words_size_pre)) (PreH19 : (words_size_pre < INT_MAX)) (PreH20 : ((Zlength (ptrs)) = words_size_pre)) (PreH21 : (problem_158_pre_z rows )) (PreH22 : (rows_well_formed_158 rows words_size_pre )) (PreH23 : (best_state_158 rows i best maxu )) (PreH24 : (seen_state_158 (Znth (i) (rows) ((@nil Z))) j seen_l unique )) ,
  (IntArray.full ( &( "seen" ) ) 256 seen_l )
  **  (CharArray.full cur ((string_length ((Znth (i) (rows) ((@nil Z))))) + 1 ) (c_string ((Znth (i) (rows) ((@nil Z))))) )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "unique" ) )) # Int  |-> unique)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "words_size" ) )) # Int  |-> words_size_pre)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "max" ) )) # Ptr  |-> max)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "maxu" ) )) # Int  |-> maxu)
  **  (PtrArray.full words_pre words_size_pre ptrs )
  **  (row_stores_missing_i_158 ptrs rows i )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition find_max_safety_wit_13 := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (seen_l: (@list Z)) (j: Z) (len: Z) (i: Z) (unique: Z) (ch: Z) (k: Z) (cur: Z) (max: Z) (best: Z) (maxu: Z) (PreH1 : ((Znth ch seen_l 0) = 0)) (PreH2 : (0 <= ((string_length ((Znth (i) (rows) ((@nil Z))))) + 1 ))) (PreH3 : (0 <= j)) (PreH4 : (j < len)) (PreH5 : (len = (string_length ((Znth (i) (rows) ((@nil Z))))))) (PreH6 : (0 <= unique)) (PreH7 : (unique <= j)) (PreH8 : (0 <= ch)) (PreH9 : (ch < 256)) (PreH10 : (ch = (Znth (j) ((Znth (i) (rows) ((@nil Z)))) (0)))) (PreH11 : (k = 256)) (PreH12 : (0 <= i)) (PreH13 : (i < words_size_pre)) (PreH14 : (cur = (Znth (i) (ptrs) (0)))) (PreH15 : (max = (Znth (best) (ptrs) (0)))) (PreH16 : (0 <= best)) (PreH17 : (best < words_size_pre)) (PreH18 : (0 < words_size_pre)) (PreH19 : (words_size_pre < INT_MAX)) (PreH20 : ((Zlength (ptrs)) = words_size_pre)) (PreH21 : (problem_158_pre_z rows )) (PreH22 : (rows_well_formed_158 rows words_size_pre )) (PreH23 : (best_state_158 rows i best maxu )) (PreH24 : (seen_state_158 (Znth (i) (rows) ((@nil Z))) j seen_l unique )) ,
  (IntArray.full ( &( "seen" ) ) 256 (replace_Znth (ch) (1) (seen_l)) )
  **  (CharArray.full cur ((string_length ((Znth (i) (rows) ((@nil Z))))) + 1 ) (c_string ((Znth (i) (rows) ((@nil Z))))) )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "unique" ) )) # Int  |-> unique)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "words_size" ) )) # Int  |-> words_size_pre)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "max" ) )) # Ptr  |-> max)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "maxu" ) )) # Int  |-> maxu)
  **  (PtrArray.full words_pre words_size_pre ptrs )
  **  (row_stores_missing_i_158 ptrs rows i )
|--
  “ ((unique + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (unique + 1 )) ”
.

Definition find_max_safety_wit_14 := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (seen_l: (@list Z)) (j: Z) (len: Z) (i: Z) (unique: Z) (ch: Z) (k: Z) (cur: Z) (max: Z) (best: Z) (maxu: Z) (PreH1 : ((Znth ch seen_l 0) = 0)) (PreH2 : (0 <= ((string_length ((Znth (i) (rows) ((@nil Z))))) + 1 ))) (PreH3 : (0 <= j)) (PreH4 : (j < len)) (PreH5 : (len = (string_length ((Znth (i) (rows) ((@nil Z))))))) (PreH6 : (0 <= unique)) (PreH7 : (unique <= j)) (PreH8 : (0 <= ch)) (PreH9 : (ch < 256)) (PreH10 : (ch = (Znth (j) ((Znth (i) (rows) ((@nil Z)))) (0)))) (PreH11 : (k = 256)) (PreH12 : (0 <= i)) (PreH13 : (i < words_size_pre)) (PreH14 : (cur = (Znth (i) (ptrs) (0)))) (PreH15 : (max = (Znth (best) (ptrs) (0)))) (PreH16 : (0 <= best)) (PreH17 : (best < words_size_pre)) (PreH18 : (0 < words_size_pre)) (PreH19 : (words_size_pre < INT_MAX)) (PreH20 : ((Zlength (ptrs)) = words_size_pre)) (PreH21 : (problem_158_pre_z rows )) (PreH22 : (rows_well_formed_158 rows words_size_pre )) (PreH23 : (best_state_158 rows i best maxu )) (PreH24 : (seen_state_158 (Znth (i) (rows) ((@nil Z))) j seen_l unique )) ,
  (IntArray.full ( &( "seen" ) ) 256 (replace_Znth (ch) (1) (seen_l)) )
  **  (CharArray.full cur ((string_length ((Znth (i) (rows) ((@nil Z))))) + 1 ) (c_string ((Znth (i) (rows) ((@nil Z))))) )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "unique" ) )) # Int  |-> unique)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "words_size" ) )) # Int  |-> words_size_pre)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "max" ) )) # Ptr  |-> max)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "maxu" ) )) # Int  |-> maxu)
  **  (PtrArray.full words_pre words_size_pre ptrs )
  **  (row_stores_missing_i_158 ptrs rows i )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition find_max_safety_wit_15 := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (seen_l: (@list Z)) (j: Z) (len: Z) (i: Z) (unique: Z) (ch: Z) (k: Z) (cur: Z) (max: Z) (best: Z) (maxu: Z) (PreH1 : ((Znth ch seen_l 0) = 0)) (PreH2 : (0 <= ((string_length ((Znth (i) (rows) ((@nil Z))))) + 1 ))) (PreH3 : (0 <= j)) (PreH4 : (j < len)) (PreH5 : (len = (string_length ((Znth (i) (rows) ((@nil Z))))))) (PreH6 : (0 <= unique)) (PreH7 : (unique <= j)) (PreH8 : (0 <= ch)) (PreH9 : (ch < 256)) (PreH10 : (ch = (Znth (j) ((Znth (i) (rows) ((@nil Z)))) (0)))) (PreH11 : (k = 256)) (PreH12 : (0 <= i)) (PreH13 : (i < words_size_pre)) (PreH14 : (cur = (Znth (i) (ptrs) (0)))) (PreH15 : (max = (Znth (best) (ptrs) (0)))) (PreH16 : (0 <= best)) (PreH17 : (best < words_size_pre)) (PreH18 : (0 < words_size_pre)) (PreH19 : (words_size_pre < INT_MAX)) (PreH20 : ((Zlength (ptrs)) = words_size_pre)) (PreH21 : (problem_158_pre_z rows )) (PreH22 : (rows_well_formed_158 rows words_size_pre )) (PreH23 : (best_state_158 rows i best maxu )) (PreH24 : (seen_state_158 (Znth (i) (rows) ((@nil Z))) j seen_l unique )) ,
  (IntArray.full ( &( "seen" ) ) 256 (replace_Znth (ch) (1) (seen_l)) )
  **  (CharArray.full cur ((string_length ((Znth (i) (rows) ((@nil Z))))) + 1 ) (c_string ((Znth (i) (rows) ((@nil Z))))) )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "unique" ) )) # Int  |-> (unique + 1 ))
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "words_size" ) )) # Int  |-> words_size_pre)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "max" ) )) # Ptr  |-> max)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "maxu" ) )) # Int  |-> maxu)
  **  (PtrArray.full words_pre words_size_pre ptrs )
  **  (row_stores_missing_i_158 ptrs rows i )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition find_max_safety_wit_16 := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (seen_l: (@list Z)) (j: Z) (len: Z) (i: Z) (unique: Z) (ch: Z) (k: Z) (cur: Z) (max: Z) (best: Z) (maxu: Z) (PreH1 : ((Znth ch seen_l 0) <> 0)) (PreH2 : (0 <= ((string_length ((Znth (i) (rows) ((@nil Z))))) + 1 ))) (PreH3 : (0 <= j)) (PreH4 : (j < len)) (PreH5 : (len = (string_length ((Znth (i) (rows) ((@nil Z))))))) (PreH6 : (0 <= unique)) (PreH7 : (unique <= j)) (PreH8 : (0 <= ch)) (PreH9 : (ch < 256)) (PreH10 : (ch = (Znth (j) ((Znth (i) (rows) ((@nil Z)))) (0)))) (PreH11 : (k = 256)) (PreH12 : (0 <= i)) (PreH13 : (i < words_size_pre)) (PreH14 : (cur = (Znth (i) (ptrs) (0)))) (PreH15 : (max = (Znth (best) (ptrs) (0)))) (PreH16 : (0 <= best)) (PreH17 : (best < words_size_pre)) (PreH18 : (0 < words_size_pre)) (PreH19 : (words_size_pre < INT_MAX)) (PreH20 : ((Zlength (ptrs)) = words_size_pre)) (PreH21 : (problem_158_pre_z rows )) (PreH22 : (rows_well_formed_158 rows words_size_pre )) (PreH23 : (best_state_158 rows i best maxu )) (PreH24 : (seen_state_158 (Znth (i) (rows) ((@nil Z))) j seen_l unique )) ,
  (IntArray.full ( &( "seen" ) ) 256 seen_l )
  **  (CharArray.full cur ((string_length ((Znth (i) (rows) ((@nil Z))))) + 1 ) (c_string ((Znth (i) (rows) ((@nil Z))))) )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "unique" ) )) # Int  |-> unique)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "words_size" ) )) # Int  |-> words_size_pre)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "max" ) )) # Ptr  |-> max)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "maxu" ) )) # Int  |-> maxu)
  **  (PtrArray.full words_pre words_size_pre ptrs )
  **  (row_stores_missing_i_158 ptrs rows i )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition find_max_safety_wit_17 := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (seen_l: (@list Z)) (i: Z) (j: Z) (len: Z) (k: Z) (cur: Z) (max: Z) (best: Z) (unique: Z) (maxu: Z) (PreH1 : (0 <= i)) (PreH2 : (i < words_size_pre)) (PreH3 : (j = len)) (PreH4 : (k = 256)) (PreH5 : (cur = (Znth (i) (ptrs) (0)))) (PreH6 : (max = (Znth (best) (ptrs) (0)))) (PreH7 : (unique = (unique_count_z_158 ((Znth (i) (rows) ((@nil Z))))))) (PreH8 : (0 < words_size_pre)) (PreH9 : (words_size_pre < INT_MAX)) (PreH10 : ((Zlength (ptrs)) = words_size_pre)) (PreH11 : (problem_158_pre_z rows )) (PreH12 : (rows_well_formed_158 rows words_size_pre )) (PreH13 : (best_state_158 rows i best maxu )) ,
  ((( &( "better" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "words_size" ) )) # Int  |-> words_size_pre)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "max" ) )) # Ptr  |-> max)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "unique" ) )) # Int  |-> unique)
  **  ((( &( "maxu" ) )) # Int  |-> maxu)
  **  (PtrArray.full words_pre words_size_pre ptrs )
  **  (row_stores_158 ptrs rows )
  **  (IntArray.full ( &( "seen" ) ) 256 seen_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition find_max_safety_wit_18 := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (seen_l: (@list Z)) (i: Z) (j: Z) (len: Z) (k: Z) (cur: Z) (max: Z) (best: Z) (unique: Z) (maxu: Z) (PreH1 : (0 <= i)) (PreH2 : (i < words_size_pre)) (PreH3 : (j = len)) (PreH4 : (k = 256)) (PreH5 : (cur = (Znth (i) (ptrs) (0)))) (PreH6 : (max = (Znth (best) (ptrs) (0)))) (PreH7 : (unique = (unique_count_z_158 ((Znth (i) (rows) ((@nil Z))))))) (PreH8 : (0 < words_size_pre)) (PreH9 : (words_size_pre < INT_MAX)) (PreH10 : ((Zlength (ptrs)) = words_size_pre)) (PreH11 : (problem_158_pre_z rows )) (PreH12 : (rows_well_formed_158 rows words_size_pre )) (PreH13 : (best_state_158 rows i best maxu )) ,
  ((( &( "cmp" ) )) # Int  |->_)
  **  ((( &( "better" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "words_size" ) )) # Int  |-> words_size_pre)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "max" ) )) # Ptr  |-> max)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "unique" ) )) # Int  |-> unique)
  **  ((( &( "maxu" ) )) # Int  |-> maxu)
  **  (PtrArray.full words_pre words_size_pre ptrs )
  **  (row_stores_158 ptrs rows )
  **  (IntArray.full ( &( "seen" ) ) 256 seen_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition find_max_safety_wit_19 := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (seen_l: (@list Z)) (i: Z) (j: Z) (len: Z) (k: Z) (cur: Z) (max: Z) (best: Z) (unique: Z) (maxu: Z) (PreH1 : (unique > maxu)) (PreH2 : (0 <= i)) (PreH3 : (i < words_size_pre)) (PreH4 : (j = len)) (PreH5 : (k = 256)) (PreH6 : (cur = (Znth (i) (ptrs) (0)))) (PreH7 : (max = (Znth (best) (ptrs) (0)))) (PreH8 : (unique = (unique_count_z_158 ((Znth (i) (rows) ((@nil Z))))))) (PreH9 : (0 < words_size_pre)) (PreH10 : (words_size_pre < INT_MAX)) (PreH11 : ((Zlength (ptrs)) = words_size_pre)) (PreH12 : (problem_158_pre_z rows )) (PreH13 : (rows_well_formed_158 rows words_size_pre )) (PreH14 : (best_state_158 rows i best maxu )) ,
  ((( &( "cmp" ) )) # Int  |-> 0)
  **  ((( &( "better" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "words_size" ) )) # Int  |-> words_size_pre)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "max" ) )) # Ptr  |-> max)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "unique" ) )) # Int  |-> unique)
  **  ((( &( "maxu" ) )) # Int  |-> maxu)
  **  (PtrArray.full words_pre words_size_pre ptrs )
  **  (row_stores_158 ptrs rows )
  **  (IntArray.full ( &( "seen" ) ) 256 seen_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition find_max_safety_wit_20 := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (seen_l: (@list Z)) (best: Z) (i: Z) (j: Z) (len: Z) (k: Z) (cur: Z) (max: Z) (better: Z) (cmp: Z) (unique: Z) (maxu: Z) (PreH1 : (0 <= best)) (PreH2 : (best < i)) (PreH3 : (i < words_size_pre)) (PreH4 : (j = len)) (PreH5 : (k = 256)) (PreH6 : (cur = (Znth (i) (ptrs) (0)))) (PreH7 : (max = (Znth (best) (ptrs) (0)))) (PreH8 : (better = 0)) (PreH9 : (unique = (unique_count_z_158 ((Znth (i) (rows) ((@nil Z))))))) (PreH10 : (unique = maxu)) (PreH11 : (strcmp_result (Znth (i) (rows) ((@nil Z))) (Znth (best) (rows) ((@nil Z))) cmp )) (PreH12 : (0 < words_size_pre)) (PreH13 : (words_size_pre < INT_MAX)) (PreH14 : ((Zlength (ptrs)) = words_size_pre)) (PreH15 : (problem_158_pre_z rows )) (PreH16 : (rows_well_formed_158 rows words_size_pre )) (PreH17 : (best_state_158 rows i best maxu )) ,
  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "words_size" ) )) # Int  |-> words_size_pre)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "max" ) )) # Ptr  |-> max)
  **  ((( &( "better" ) )) # Int  |-> better)
  **  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "unique" ) )) # Int  |-> unique)
  **  ((( &( "maxu" ) )) # Int  |-> maxu)
  **  (PtrArray.full words_pre words_size_pre ptrs )
  **  (row_stores_158 ptrs rows )
  **  (IntArray.full ( &( "seen" ) ) 256 seen_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition find_max_safety_wit_21 := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (seen_l: (@list Z)) (best: Z) (i: Z) (j: Z) (len: Z) (k: Z) (cur: Z) (max: Z) (better: Z) (cmp: Z) (unique: Z) (maxu: Z) (PreH1 : (cmp < 0)) (PreH2 : (0 <= best)) (PreH3 : (best < i)) (PreH4 : (i < words_size_pre)) (PreH5 : (j = len)) (PreH6 : (k = 256)) (PreH7 : (cur = (Znth (i) (ptrs) (0)))) (PreH8 : (max = (Znth (best) (ptrs) (0)))) (PreH9 : (better = 0)) (PreH10 : (unique = (unique_count_z_158 ((Znth (i) (rows) ((@nil Z))))))) (PreH11 : (unique = maxu)) (PreH12 : (strcmp_result (Znth (i) (rows) ((@nil Z))) (Znth (best) (rows) ((@nil Z))) cmp )) (PreH13 : (0 < words_size_pre)) (PreH14 : (words_size_pre < INT_MAX)) (PreH15 : ((Zlength (ptrs)) = words_size_pre)) (PreH16 : (problem_158_pre_z rows )) (PreH17 : (rows_well_formed_158 rows words_size_pre )) (PreH18 : (best_state_158 rows i best maxu )) ,
  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "words_size" ) )) # Int  |-> words_size_pre)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "max" ) )) # Ptr  |-> max)
  **  ((( &( "better" ) )) # Int  |-> better)
  **  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "unique" ) )) # Int  |-> unique)
  **  ((( &( "maxu" ) )) # Int  |-> maxu)
  **  (PtrArray.full words_pre words_size_pre ptrs )
  **  (row_stores_158 ptrs rows )
  **  (IntArray.full ( &( "seen" ) ) 256 seen_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition find_max_safety_wit_22 := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (seen_l: (@list Z)) (i: Z) (j: Z) (len: Z) (k: Z) (cur: Z) (max: Z) (best: Z) (unique: Z) (maxu: Z) (PreH1 : (unique > maxu)) (PreH2 : (0 <= i)) (PreH3 : (i < words_size_pre)) (PreH4 : (j = len)) (PreH5 : (k = 256)) (PreH6 : (cur = (Znth (i) (ptrs) (0)))) (PreH7 : (max = (Znth (best) (ptrs) (0)))) (PreH8 : (unique = (unique_count_z_158 ((Znth (i) (rows) ((@nil Z))))))) (PreH9 : (0 < words_size_pre)) (PreH10 : (words_size_pre < INT_MAX)) (PreH11 : ((Zlength (ptrs)) = words_size_pre)) (PreH12 : (problem_158_pre_z rows )) (PreH13 : (rows_well_formed_158 rows words_size_pre )) (PreH14 : (best_state_158 rows i best maxu )) ,
  ((( &( "cmp" ) )) # Int  |-> 0)
  **  ((( &( "better" ) )) # Int  |-> 1)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "words_size" ) )) # Int  |-> words_size_pre)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "max" ) )) # Ptr  |-> max)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "unique" ) )) # Int  |-> unique)
  **  ((( &( "maxu" ) )) # Int  |-> maxu)
  **  (PtrArray.full words_pre words_size_pre ptrs )
  **  (row_stores_158 ptrs rows )
  **  (IntArray.full ( &( "seen" ) ) 256 seen_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition find_max_safety_wit_23 := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (seen_l: (@list Z)) (best: Z) (i: Z) (j: Z) (len: Z) (k: Z) (cur: Z) (max: Z) (better: Z) (cmp: Z) (unique: Z) (maxu: Z) (PreH1 : (cmp < 0)) (PreH2 : (0 <= best)) (PreH3 : (best < i)) (PreH4 : (i < words_size_pre)) (PreH5 : (j = len)) (PreH6 : (k = 256)) (PreH7 : (cur = (Znth (i) (ptrs) (0)))) (PreH8 : (max = (Znth (best) (ptrs) (0)))) (PreH9 : (better = 0)) (PreH10 : (unique = (unique_count_z_158 ((Znth (i) (rows) ((@nil Z))))))) (PreH11 : (unique = maxu)) (PreH12 : (strcmp_result (Znth (i) (rows) ((@nil Z))) (Znth (best) (rows) ((@nil Z))) cmp )) (PreH13 : (0 < words_size_pre)) (PreH14 : (words_size_pre < INT_MAX)) (PreH15 : ((Zlength (ptrs)) = words_size_pre)) (PreH16 : (problem_158_pre_z rows )) (PreH17 : (rows_well_formed_158 rows words_size_pre )) (PreH18 : (best_state_158 rows i best maxu )) ,
  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "words_size" ) )) # Int  |-> words_size_pre)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "max" ) )) # Ptr  |-> max)
  **  ((( &( "better" ) )) # Int  |-> 1)
  **  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "unique" ) )) # Int  |-> unique)
  **  ((( &( "maxu" ) )) # Int  |-> maxu)
  **  (PtrArray.full words_pre words_size_pre ptrs )
  **  (row_stores_158 ptrs rows )
  **  (IntArray.full ( &( "seen" ) ) 256 seen_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition find_max_safety_wit_24 := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (seen_l: (@list Z)) (best: Z) (i: Z) (j: Z) (len: Z) (k: Z) (cur: Z) (max: Z) (better: Z) (cmp: Z) (unique: Z) (maxu: Z) (PreH1 : (cmp >= 0)) (PreH2 : (0 <= best)) (PreH3 : (best < i)) (PreH4 : (i < words_size_pre)) (PreH5 : (j = len)) (PreH6 : (k = 256)) (PreH7 : (cur = (Znth (i) (ptrs) (0)))) (PreH8 : (max = (Znth (best) (ptrs) (0)))) (PreH9 : (better = 0)) (PreH10 : (unique = (unique_count_z_158 ((Znth (i) (rows) ((@nil Z))))))) (PreH11 : (unique = maxu)) (PreH12 : (strcmp_result (Znth (i) (rows) ((@nil Z))) (Znth (best) (rows) ((@nil Z))) cmp )) (PreH13 : (0 < words_size_pre)) (PreH14 : (words_size_pre < INT_MAX)) (PreH15 : ((Zlength (ptrs)) = words_size_pre)) (PreH16 : (problem_158_pre_z rows )) (PreH17 : (rows_well_formed_158 rows words_size_pre )) (PreH18 : (best_state_158 rows i best maxu )) ,
  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "words_size" ) )) # Int  |-> words_size_pre)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "max" ) )) # Ptr  |-> max)
  **  ((( &( "better" ) )) # Int  |-> better)
  **  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "unique" ) )) # Int  |-> unique)
  **  ((( &( "maxu" ) )) # Int  |-> maxu)
  **  (PtrArray.full words_pre words_size_pre ptrs )
  **  (row_stores_158 ptrs rows )
  **  (IntArray.full ( &( "seen" ) ) 256 seen_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition find_max_safety_wit_25 := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (seen_l: (@list Z)) (i: Z) (j: Z) (len: Z) (k: Z) (cur: Z) (max: Z) (best: Z) (unique: Z) (maxu: Z) (PreH1 : (unique <> maxu)) (PreH2 : (unique <= maxu)) (PreH3 : (0 <= i)) (PreH4 : (i < words_size_pre)) (PreH5 : (j = len)) (PreH6 : (k = 256)) (PreH7 : (cur = (Znth (i) (ptrs) (0)))) (PreH8 : (max = (Znth (best) (ptrs) (0)))) (PreH9 : (unique = (unique_count_z_158 ((Znth (i) (rows) ((@nil Z))))))) (PreH10 : (0 < words_size_pre)) (PreH11 : (words_size_pre < INT_MAX)) (PreH12 : ((Zlength (ptrs)) = words_size_pre)) (PreH13 : (problem_158_pre_z rows )) (PreH14 : (rows_well_formed_158 rows words_size_pre )) (PreH15 : (best_state_158 rows i best maxu )) ,
  ((( &( "cmp" ) )) # Int  |-> 0)
  **  ((( &( "better" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "words_size" ) )) # Int  |-> words_size_pre)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "max" ) )) # Ptr  |-> max)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "unique" ) )) # Int  |-> unique)
  **  ((( &( "maxu" ) )) # Int  |-> maxu)
  **  (PtrArray.full words_pre words_size_pre ptrs )
  **  (row_stores_158 ptrs rows )
  **  (IntArray.full ( &( "seen" ) ) 256 seen_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition find_max_safety_wit_26 := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (seen_l: (@list Z)) (i: Z) (j: Z) (len: Z) (k: Z) (cur: Z) (max: Z) (best: Z) (unique: Z) (maxu: Z) (PreH1 : (i = best)) (PreH2 : (unique = maxu)) (PreH3 : (unique <= maxu)) (PreH4 : (0 <= i)) (PreH5 : (i < words_size_pre)) (PreH6 : (j = len)) (PreH7 : (k = 256)) (PreH8 : (cur = (Znth (i) (ptrs) (0)))) (PreH9 : (max = (Znth (best) (ptrs) (0)))) (PreH10 : (unique = (unique_count_z_158 ((Znth (i) (rows) ((@nil Z))))))) (PreH11 : (0 < words_size_pre)) (PreH12 : (words_size_pre < INT_MAX)) (PreH13 : ((Zlength (ptrs)) = words_size_pre)) (PreH14 : (problem_158_pre_z rows )) (PreH15 : (rows_well_formed_158 rows words_size_pre )) (PreH16 : (best_state_158 rows i best maxu )) ,
  ((( &( "cmp" ) )) # Int  |-> 0)
  **  ((( &( "better" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "words_size" ) )) # Int  |-> words_size_pre)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "max" ) )) # Ptr  |-> max)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "unique" ) )) # Int  |-> unique)
  **  ((( &( "maxu" ) )) # Int  |-> maxu)
  **  (PtrArray.full words_pre words_size_pre ptrs )
  **  (row_stores_158 ptrs rows )
  **  (IntArray.full ( &( "seen" ) ) 256 seen_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition find_max_safety_wit_27 := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (seen_l: (@list Z)) (best: Z) (i: Z) (j: Z) (len: Z) (k: Z) (cur: Z) (max: Z) (better: Z) (cmp: Z) (unique: Z) (maxu: Z) (PreH1 : (better <> 0)) (PreH2 : (cmp >= 0)) (PreH3 : (0 <= best)) (PreH4 : (best < i)) (PreH5 : (i < words_size_pre)) (PreH6 : (j = len)) (PreH7 : (k = 256)) (PreH8 : (cur = (Znth (i) (ptrs) (0)))) (PreH9 : (max = (Znth (best) (ptrs) (0)))) (PreH10 : (better = 0)) (PreH11 : (unique = (unique_count_z_158 ((Znth (i) (rows) ((@nil Z))))))) (PreH12 : (unique = maxu)) (PreH13 : (strcmp_result (Znth (i) (rows) ((@nil Z))) (Znth (best) (rows) ((@nil Z))) cmp )) (PreH14 : (0 < words_size_pre)) (PreH15 : (words_size_pre < INT_MAX)) (PreH16 : ((Zlength (ptrs)) = words_size_pre)) (PreH17 : (problem_158_pre_z rows )) (PreH18 : (rows_well_formed_158 rows words_size_pre )) (PreH19 : (best_state_158 rows i best maxu )) ,
  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "words_size" ) )) # Int  |-> words_size_pre)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "max" ) )) # Ptr  |-> max)
  **  ((( &( "better" ) )) # Int  |-> better)
  **  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "unique" ) )) # Int  |-> unique)
  **  ((( &( "maxu" ) )) # Int  |-> maxu)
  **  (PtrArray.full words_pre words_size_pre ptrs )
  **  (row_stores_158 ptrs rows )
  **  (IntArray.full ( &( "seen" ) ) 256 seen_l )
|--
  “ False ”
.

Definition find_max_safety_wit_28 := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (i: Z) (best: Z) (max: Z) (maxu: Z) (PreH1 : (0 <= i)) (PreH2 : (i < words_size_pre)) (PreH3 : (0 < words_size_pre)) (PreH4 : (words_size_pre < INT_MAX)) (PreH5 : ((Zlength (ptrs)) = words_size_pre)) (PreH6 : (rows_well_formed_158 rows words_size_pre )) (PreH7 : (problem_158_pre_z rows )) (PreH8 : (0 <= best)) (PreH9 : (best < words_size_pre)) (PreH10 : (max = (Znth (best) (ptrs) (0)))) (PreH11 : (best_state_158 rows (i + 1 ) best maxu )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "words_size" ) )) # Int  |-> words_size_pre)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "max" ) )) # Ptr  |-> max)
  **  ((( &( "maxu" ) )) # Int  |-> maxu)
  **  (PtrArray.full words_pre words_size_pre ptrs )
  **  (row_stores_158 ptrs rows )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition find_max_entail_wit_1 := 
(
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (PreH1 : (0 < words_size_pre)) (PreH2 : (words_size_pre < INT_MAX)) (PreH3 : ((Zlength (ptrs)) = words_size_pre)) (PreH4 : (rows_well_formed_158 rows words_size_pre )) (PreH5 : (problem_158_pre_z rows )) ,
  (PtrArray.full words_pre words_size_pre ptrs )
  **  (row_stores_158 ptrs rows )
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= words_size_pre) ” 
  &&  “ (0 < words_size_pre) ” 
  &&  “ (words_size_pre < INT_MAX) ” 
  &&  “ ((Zlength (ptrs)) = words_size_pre) ” 
  &&  “ (rows_well_formed_158 rows words_size_pre ) ” 
  &&  “ (problem_158_pre_z rows ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 < words_size_pre) ” 
  &&  “ ((Znth 0 ptrs 0) = (Znth (0) (ptrs) (0))) ” 
  &&  “ (best_state_158 rows 0 0 0 ) ”
  &&  (PtrArray.full words_pre words_size_pre ptrs )
  **  (row_stores_158 ptrs rows )
) \/
(
forall (words_size_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (PreH1 : (0 < words_size_pre)) (PreH2 : (words_size_pre < INT_MAX)) (PreH3 : ((Zlength (ptrs)) = words_size_pre)) (PreH4 : (rows_well_formed_158 rows words_size_pre )) (PreH5 : (problem_158_pre_z rows )) ,
  (row_stores_158 ptrs rows )
|--
  “ (best_state_158 rows 0 0 0 ) ” 
  &&  “ ((Znth 0 ptrs 0) = (Znth (0) (ptrs) (0))) ”
  &&  (row_stores_158 ptrs rows )
).

Definition find_max_entail_wit_1_split_goal_1 := 
forall (words_size_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (PreH1 : (0 < words_size_pre)) (PreH2 : (words_size_pre < INT_MAX)) (PreH3 : ((Zlength (ptrs)) = words_size_pre)) (PreH4 : (rows_well_formed_158 rows words_size_pre )) (PreH5 : (problem_158_pre_z rows )) ,
  (row_stores_158 ptrs rows )
|--
  “ (best_state_158 rows 0 0 0 ) ”
.

Definition find_max_entail_wit_1_split_goal_2 := 
forall (words_size_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (PreH1 : (0 < words_size_pre)) (PreH2 : (words_size_pre < INT_MAX)) (PreH3 : ((Zlength (ptrs)) = words_size_pre)) (PreH4 : (rows_well_formed_158 rows words_size_pre )) (PreH5 : (problem_158_pre_z rows )) ,
  (row_stores_158 ptrs rows )
|--
  “ ((Znth 0 ptrs 0) = (Znth (0) (ptrs) (0))) ”
.

Definition find_max_entail_wit_1_split_goal_spatial := 
forall (words_size_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (PreH1 : (0 < words_size_pre)) (PreH2 : (words_size_pre < INT_MAX)) (PreH3 : ((Zlength (ptrs)) = words_size_pre)) (PreH4 : (rows_well_formed_158 rows words_size_pre )) (PreH5 : (problem_158_pre_z rows )) ,
  (row_stores_158 ptrs rows )
|--
  (row_stores_158 ptrs rows )
.

Definition find_max_entail_wit_2 := 
(
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (maxu: Z) (max: Z) (best: Z) (i: Z) (PreH1 : (i < words_size_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= words_size_pre)) (PreH4 : (0 < words_size_pre)) (PreH5 : (words_size_pre < INT_MAX)) (PreH6 : ((Zlength (ptrs)) = words_size_pre)) (PreH7 : (rows_well_formed_158 rows words_size_pre )) (PreH8 : (problem_158_pre_z rows )) (PreH9 : (0 <= best)) (PreH10 : (best < words_size_pre)) (PreH11 : (max = (Znth (best) (ptrs) (0)))) (PreH12 : (best_state_158 rows i best maxu )) ,
  (IntArray.undef_full ( &( "seen" ) ) 256 )
  **  (PtrArray.full words_pre words_size_pre ptrs )
  **  (row_stores_158 ptrs rows )
|--
  EX (zeros: (@list Z)) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= 256) ” 
  &&  “ (zeros = (repeat_Z (0) (0))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < words_size_pre) ” 
  &&  “ ((Znth i ptrs 0) = (Znth (i) (ptrs) (0))) ” 
  &&  “ (max = (Znth (best) (ptrs) (0))) ” 
  &&  “ (0 < words_size_pre) ” 
  &&  “ (words_size_pre < INT_MAX) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best < words_size_pre) ” 
  &&  “ ((Zlength (ptrs)) = words_size_pre) ” 
  &&  “ (rows_well_formed_158 rows words_size_pre ) ” 
  &&  “ (problem_158_pre_z rows ) ” 
  &&  “ (best_state_158 rows i best maxu ) ”
  &&  (PtrArray.full words_pre words_size_pre ptrs )
  **  (row_stores_158 ptrs rows )
  **  (IntArray.seg ( &( "seen" ) ) 0 0 zeros )
  **  (IntArray.undef_seg ( &( "seen" ) ) 0 256 )
) \/
(
forall (words_size_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (maxu: Z) (max: Z) (best: Z) (i: Z) (PreH1 : (i < words_size_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= words_size_pre)) (PreH4 : (0 < words_size_pre)) (PreH5 : (words_size_pre < INT_MAX)) (PreH6 : ((Zlength (ptrs)) = words_size_pre)) (PreH7 : (rows_well_formed_158 rows words_size_pre )) (PreH8 : (problem_158_pre_z rows )) (PreH9 : (0 <= best)) (PreH10 : (best < words_size_pre)) (PreH11 : (max = (Znth (best) (ptrs) (0)))) (PreH12 : (best_state_158 rows i best maxu )) ,
  (row_stores_158 ptrs rows )
|--
  “ ((Znth i ptrs 0) = (Znth (i) (ptrs) (0))) ” 
  &&  “ ((@nil Z) = (repeat_Z (0) (0))) ”
  &&  (row_stores_158 ptrs rows )
).

Definition find_max_entail_wit_2_split_goal_1 := 
forall (words_size_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (maxu: Z) (max: Z) (best: Z) (i: Z) (PreH1 : (i < words_size_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= words_size_pre)) (PreH4 : (0 < words_size_pre)) (PreH5 : (words_size_pre < INT_MAX)) (PreH6 : ((Zlength (ptrs)) = words_size_pre)) (PreH7 : (rows_well_formed_158 rows words_size_pre )) (PreH8 : (problem_158_pre_z rows )) (PreH9 : (0 <= best)) (PreH10 : (best < words_size_pre)) (PreH11 : (max = (Znth (best) (ptrs) (0)))) (PreH12 : (best_state_158 rows i best maxu )) ,
  (row_stores_158 ptrs rows )
|--
  “ ((Znth i ptrs 0) = (Znth (i) (ptrs) (0))) ”
.

Definition find_max_entail_wit_2_split_goal_2 := 
forall (words_size_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (maxu: Z) (max: Z) (best: Z) (i: Z) (PreH1 : (i < words_size_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= words_size_pre)) (PreH4 : (0 < words_size_pre)) (PreH5 : (words_size_pre < INT_MAX)) (PreH6 : ((Zlength (ptrs)) = words_size_pre)) (PreH7 : (rows_well_formed_158 rows words_size_pre )) (PreH8 : (problem_158_pre_z rows )) (PreH9 : (0 <= best)) (PreH10 : (best < words_size_pre)) (PreH11 : (max = (Znth (best) (ptrs) (0)))) (PreH12 : (best_state_158 rows i best maxu )) ,
  (row_stores_158 ptrs rows )
|--
  “ ((@nil Z) = (repeat_Z (0) (0))) ”
.

Definition find_max_entail_wit_2_split_goal_spatial := 
forall (words_size_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (maxu: Z) (max: Z) (best: Z) (i: Z) (PreH1 : (i < words_size_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= words_size_pre)) (PreH4 : (0 < words_size_pre)) (PreH5 : (words_size_pre < INT_MAX)) (PreH6 : ((Zlength (ptrs)) = words_size_pre)) (PreH7 : (rows_well_formed_158 rows words_size_pre )) (PreH8 : (problem_158_pre_z rows )) (PreH9 : (0 <= best)) (PreH10 : (best < words_size_pre)) (PreH11 : (max = (Znth (best) (ptrs) (0)))) (PreH12 : (best_state_158 rows i best maxu )) ,
  (row_stores_158 ptrs rows )
|--
  (row_stores_158 ptrs rows )
.

Definition find_max_entail_wit_3 := 
(
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (maxu: Z) (best: Z) (max: Z) (cur: Z) (i: Z) (zeros_2: (@list Z)) (k: Z) (PreH1 : (k < 256)) (PreH2 : (0 <= k)) (PreH3 : (k <= 256)) (PreH4 : (zeros_2 = (repeat_Z (0) (k)))) (PreH5 : (0 <= i)) (PreH6 : (i < words_size_pre)) (PreH7 : (cur = (Znth (i) (ptrs) (0)))) (PreH8 : (max = (Znth (best) (ptrs) (0)))) (PreH9 : (0 < words_size_pre)) (PreH10 : (words_size_pre < INT_MAX)) (PreH11 : (0 <= best)) (PreH12 : (best < words_size_pre)) (PreH13 : ((Zlength (ptrs)) = words_size_pre)) (PreH14 : (rows_well_formed_158 rows words_size_pre )) (PreH15 : (problem_158_pre_z rows )) (PreH16 : (best_state_158 rows i best maxu )) ,
  (IntArray.seg ( &( "seen" ) ) 0 (k + 1 ) (app (zeros_2) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "seen" ) ) (k + 1 ) 256 )
  **  (PtrArray.full words_pre words_size_pre ptrs )
  **  (row_stores_158 ptrs rows )
|--
  EX (zeros: (@list Z)) ,
  “ (0 <= (k + 1 )) ” 
  &&  “ ((k + 1 ) <= 256) ” 
  &&  “ (zeros = (repeat_Z (0) ((k + 1 )))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < words_size_pre) ” 
  &&  “ (cur = (Znth (i) (ptrs) (0))) ” 
  &&  “ (max = (Znth (best) (ptrs) (0))) ” 
  &&  “ (0 < words_size_pre) ” 
  &&  “ (words_size_pre < INT_MAX) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best < words_size_pre) ” 
  &&  “ ((Zlength (ptrs)) = words_size_pre) ” 
  &&  “ (rows_well_formed_158 rows words_size_pre ) ” 
  &&  “ (problem_158_pre_z rows ) ” 
  &&  “ (best_state_158 rows i best maxu ) ”
  &&  (PtrArray.full words_pre words_size_pre ptrs )
  **  (row_stores_158 ptrs rows )
  **  (IntArray.seg ( &( "seen" ) ) 0 (k + 1 ) zeros )
  **  (IntArray.undef_seg ( &( "seen" ) ) (k + 1 ) 256 )
) \/
(
forall (words_size_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (maxu: Z) (best: Z) (max: Z) (cur: Z) (i: Z) (zeros_2: (@list Z)) (k: Z) (PreH1 : (k < 256)) (PreH2 : (0 <= k)) (PreH3 : (k <= 256)) (PreH4 : (zeros_2 = (repeat_Z (0) (k)))) (PreH5 : (0 <= i)) (PreH6 : (i < words_size_pre)) (PreH7 : (cur = (Znth (i) (ptrs) (0)))) (PreH8 : (max = (Znth (best) (ptrs) (0)))) (PreH9 : (0 < words_size_pre)) (PreH10 : (words_size_pre < INT_MAX)) (PreH11 : (0 <= best)) (PreH12 : (best < words_size_pre)) (PreH13 : ((Zlength (ptrs)) = words_size_pre)) (PreH14 : (rows_well_formed_158 rows words_size_pre )) (PreH15 : (problem_158_pre_z rows )) (PreH16 : (best_state_158 rows i best maxu )) ,
  (row_stores_158 ptrs rows )
|--
  “ ((app (zeros_2) ((cons (0) ((@nil Z))))) = (repeat_Z (0) ((k + 1 )))) ”
  &&  (row_stores_158 ptrs rows )
).

Definition find_max_entail_wit_3_split_goal_1 := 
forall (words_size_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (maxu: Z) (best: Z) (max: Z) (cur: Z) (i: Z) (zeros_2: (@list Z)) (k: Z) (PreH1 : (k < 256)) (PreH2 : (0 <= k)) (PreH3 : (k <= 256)) (PreH4 : (zeros_2 = (repeat_Z (0) (k)))) (PreH5 : (0 <= i)) (PreH6 : (i < words_size_pre)) (PreH7 : (cur = (Znth (i) (ptrs) (0)))) (PreH8 : (max = (Znth (best) (ptrs) (0)))) (PreH9 : (0 < words_size_pre)) (PreH10 : (words_size_pre < INT_MAX)) (PreH11 : (0 <= best)) (PreH12 : (best < words_size_pre)) (PreH13 : ((Zlength (ptrs)) = words_size_pre)) (PreH14 : (rows_well_formed_158 rows words_size_pre )) (PreH15 : (problem_158_pre_z rows )) (PreH16 : (best_state_158 rows i best maxu )) ,
  (row_stores_158 ptrs rows )
|--
  “ ((app (zeros_2) ((cons (0) ((@nil Z))))) = (repeat_Z (0) ((k + 1 )))) ”
.

Definition find_max_entail_wit_3_split_goal_spatial := 
forall (words_size_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (maxu: Z) (best: Z) (max: Z) (cur: Z) (i: Z) (zeros_2: (@list Z)) (k: Z) (PreH1 : (k < 256)) (PreH2 : (0 <= k)) (PreH3 : (k <= 256)) (PreH4 : (zeros_2 = (repeat_Z (0) (k)))) (PreH5 : (0 <= i)) (PreH6 : (i < words_size_pre)) (PreH7 : (cur = (Znth (i) (ptrs) (0)))) (PreH8 : (max = (Znth (best) (ptrs) (0)))) (PreH9 : (0 < words_size_pre)) (PreH10 : (words_size_pre < INT_MAX)) (PreH11 : (0 <= best)) (PreH12 : (best < words_size_pre)) (PreH13 : ((Zlength (ptrs)) = words_size_pre)) (PreH14 : (rows_well_formed_158 rows words_size_pre )) (PreH15 : (problem_158_pre_z rows )) (PreH16 : (best_state_158 rows i best maxu )) ,
  (row_stores_158 ptrs rows )
|--
  (row_stores_158 ptrs rows )
.

Definition find_max_entail_wit_4 := 
(
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (maxu: Z) (best: Z) (max: Z) (cur: Z) (i: Z) (zeros: (@list Z)) (k: Z) (PreH1 : (k >= 256)) (PreH2 : (0 <= k)) (PreH3 : (k <= 256)) (PreH4 : (zeros = (repeat_Z (0) (k)))) (PreH5 : (0 <= i)) (PreH6 : (i < words_size_pre)) (PreH7 : (cur = (Znth (i) (ptrs) (0)))) (PreH8 : (max = (Znth (best) (ptrs) (0)))) (PreH9 : (0 < words_size_pre)) (PreH10 : (words_size_pre < INT_MAX)) (PreH11 : (0 <= best)) (PreH12 : (best < words_size_pre)) (PreH13 : ((Zlength (ptrs)) = words_size_pre)) (PreH14 : (rows_well_formed_158 rows words_size_pre )) (PreH15 : (problem_158_pre_z rows )) (PreH16 : (best_state_158 rows i best maxu )) ,
  (PtrArray.full words_pre words_size_pre ptrs )
  **  (row_stores_158 ptrs rows )
  **  (IntArray.seg ( &( "seen" ) ) 0 k zeros )
  **  (IntArray.undef_seg ( &( "seen" ) ) k 256 )
|--
  “ (0 <= i) ” 
  &&  “ (i < words_size_pre) ” 
  &&  “ (k = 256) ” 
  &&  “ (cur = (Znth (i) (ptrs) (0))) ” 
  &&  “ (max = (Znth (best) (ptrs) (0))) ” 
  &&  “ (0 < words_size_pre) ” 
  &&  “ (words_size_pre < INT_MAX) ” 
  &&  “ ((Zlength (ptrs)) = words_size_pre) ” 
  &&  “ (problem_158_pre_z rows ) ” 
  &&  “ (rows_well_formed_158 rows words_size_pre ) ” 
  &&  “ (best_state_158 rows i best maxu ) ”
  &&  (PtrArray.full words_pre words_size_pre ptrs )
  **  (row_stores_missing_i_158 ptrs rows i )
  **  (store_string cur (Znth (i) (rows) ((@nil Z))) )
  **  (IntArray.full ( &( "seen" ) ) 256 (repeat_Z (0) (256)) )
) \/
(
forall (words_size_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (maxu: Z) (best: Z) (max: Z) (cur: Z) (i: Z) (zeros: (@list Z)) (k: Z) (PreH1 : (k >= 256)) (PreH2 : (0 <= k)) (PreH3 : (k <= 256)) (PreH4 : (zeros = (repeat_Z (0) (k)))) (PreH5 : (0 <= i)) (PreH6 : (i < words_size_pre)) (PreH7 : (cur = (Znth (i) (ptrs) (0)))) (PreH8 : (max = (Znth (best) (ptrs) (0)))) (PreH9 : (0 < words_size_pre)) (PreH10 : (words_size_pre < INT_MAX)) (PreH11 : (0 <= best)) (PreH12 : (best < words_size_pre)) (PreH13 : ((Zlength (ptrs)) = words_size_pre)) (PreH14 : (rows_well_formed_158 rows words_size_pre )) (PreH15 : (problem_158_pre_z rows )) (PreH16 : (best_state_158 rows i best maxu )) ,
  (row_stores_158 ptrs rows )
  **  (IntArray.seg ( &( "seen" ) ) 0 k zeros )
|--
  (CharArray.full cur ((string_length ((Znth (i) (rows) ((@nil Z))))) + 1 ) (c_string ((Znth (i) (rows) ((@nil Z))))) )
  **  (row_stores_missing_i_158 ptrs rows i )
  **  (IntArray.full ( &( "seen" ) ) 256 (repeat_Z (0) (256)) )
).

Definition find_max_entail_wit_4_split_goal_spatial := 
forall (words_size_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (maxu: Z) (best: Z) (max: Z) (cur: Z) (i: Z) (zeros: (@list Z)) (k: Z) (PreH1 : (k >= 256)) (PreH2 : (0 <= k)) (PreH3 : (k <= 256)) (PreH4 : (zeros = (repeat_Z (0) (k)))) (PreH5 : (0 <= i)) (PreH6 : (i < words_size_pre)) (PreH7 : (cur = (Znth (i) (ptrs) (0)))) (PreH8 : (max = (Znth (best) (ptrs) (0)))) (PreH9 : (0 < words_size_pre)) (PreH10 : (words_size_pre < INT_MAX)) (PreH11 : (0 <= best)) (PreH12 : (best < words_size_pre)) (PreH13 : ((Zlength (ptrs)) = words_size_pre)) (PreH14 : (rows_well_formed_158 rows words_size_pre )) (PreH15 : (problem_158_pre_z rows )) (PreH16 : (best_state_158 rows i best maxu )) ,
  (row_stores_158 ptrs rows )
  **  (IntArray.seg ( &( "seen" ) ) 0 k zeros )
|--
  (CharArray.full cur ((string_length ((Znth (i) (rows) ((@nil Z))))) + 1 ) (c_string ((Znth (i) (rows) ((@nil Z))))) )
  **  (row_stores_missing_i_158 ptrs rows i )
  **  (IntArray.full ( &( "seen" ) ) 256 (repeat_Z (0) (256)) )
.

Definition find_max_entail_wit_5 := 
(
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (i: Z) (k: Z) (cur: Z) (max: Z) (best: Z) (maxu: Z) (retval: Z) (PreH1 : (retval = (string_length ((Znth (i) (rows) ((@nil Z))))))) (PreH2 : (0 <= ((string_length ((Znth (i) (rows) ((@nil Z))))) + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < words_size_pre)) (PreH5 : (k = 256)) (PreH6 : (cur = (Znth (i) (ptrs) (0)))) (PreH7 : (max = (Znth (best) (ptrs) (0)))) (PreH8 : (0 < words_size_pre)) (PreH9 : (words_size_pre < INT_MAX)) (PreH10 : ((Zlength (ptrs)) = words_size_pre)) (PreH11 : (problem_158_pre_z rows )) (PreH12 : (rows_well_formed_158 rows words_size_pre )) (PreH13 : (best_state_158 rows i best maxu )) ,
  (store_string cur (Znth (i) (rows) ((@nil Z))) )
  **  (PtrArray.full words_pre words_size_pre ptrs )
  **  (row_stores_missing_i_158 ptrs rows i )
  **  (IntArray.full ( &( "seen" ) ) 256 (repeat_Z (0) (256)) )
|--
  EX (seen_l: (@list Z)) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval = (string_length ((Znth (i) (rows) ((@nil Z)))))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (k = 256) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < words_size_pre) ” 
  &&  “ (cur = (Znth (i) (ptrs) (0))) ” 
  &&  “ (max = (Znth (best) (ptrs) (0))) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best < words_size_pre) ” 
  &&  “ (0 < words_size_pre) ” 
  &&  “ (words_size_pre < INT_MAX) ” 
  &&  “ ((Zlength (ptrs)) = words_size_pre) ” 
  &&  “ (problem_158_pre_z rows ) ” 
  &&  “ (rows_well_formed_158 rows words_size_pre ) ” 
  &&  “ (best_state_158 rows i best maxu ) ” 
  &&  “ (seen_state_158 (Znth (i) (rows) ((@nil Z))) 0 seen_l 0 ) ”
  &&  (PtrArray.full words_pre words_size_pre ptrs )
  **  (row_stores_missing_i_158 ptrs rows i )
  **  (store_string cur (Znth (i) (rows) ((@nil Z))) )
  **  (IntArray.full ( &( "seen" ) ) 256 seen_l )
) \/
(
forall (words_size_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (i: Z) (k: Z) (cur: Z) (max: Z) (best: Z) (maxu: Z) (retval: Z) (PreH1 : (retval = (string_length ((Znth (i) (rows) ((@nil Z))))))) (PreH2 : (0 <= ((string_length ((Znth (i) (rows) ((@nil Z))))) + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < words_size_pre)) (PreH5 : (k = 256)) (PreH6 : (cur = (Znth (i) (ptrs) (0)))) (PreH7 : (max = (Znth (best) (ptrs) (0)))) (PreH8 : (0 < words_size_pre)) (PreH9 : (words_size_pre < INT_MAX)) (PreH10 : ((Zlength (ptrs)) = words_size_pre)) (PreH11 : (problem_158_pre_z rows )) (PreH12 : (rows_well_formed_158 rows words_size_pre )) (PreH13 : (best_state_158 rows i best maxu )) ,
  (row_stores_missing_i_158 ptrs rows i )
|--
  “ (seen_state_158 (Znth (i) (rows) ((@nil Z))) 0 (repeat_Z (0) (256)) 0 ) ” 
  &&  “ (best < words_size_pre) ” 
  &&  “ (0 <= best) ” 
  &&  “ (0 <= retval) ”
  &&  (row_stores_missing_i_158 ptrs rows i )
).

Definition find_max_entail_wit_5_split_goal_1 := 
forall (words_size_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (i: Z) (k: Z) (cur: Z) (max: Z) (best: Z) (maxu: Z) (retval: Z) (PreH1 : (retval = (string_length ((Znth (i) (rows) ((@nil Z))))))) (PreH2 : (0 <= ((string_length ((Znth (i) (rows) ((@nil Z))))) + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < words_size_pre)) (PreH5 : (k = 256)) (PreH6 : (cur = (Znth (i) (ptrs) (0)))) (PreH7 : (max = (Znth (best) (ptrs) (0)))) (PreH8 : (0 < words_size_pre)) (PreH9 : (words_size_pre < INT_MAX)) (PreH10 : ((Zlength (ptrs)) = words_size_pre)) (PreH11 : (problem_158_pre_z rows )) (PreH12 : (rows_well_formed_158 rows words_size_pre )) (PreH13 : (best_state_158 rows i best maxu )) ,
  (row_stores_missing_i_158 ptrs rows i )
|--
  “ (seen_state_158 (Znth (i) (rows) ((@nil Z))) 0 (repeat_Z (0) (256)) 0 ) ”
.

Definition find_max_entail_wit_5_split_goal_2 := 
forall (words_size_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (i: Z) (k: Z) (cur: Z) (max: Z) (best: Z) (maxu: Z) (retval: Z) (PreH1 : (retval = (string_length ((Znth (i) (rows) ((@nil Z))))))) (PreH2 : (0 <= ((string_length ((Znth (i) (rows) ((@nil Z))))) + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < words_size_pre)) (PreH5 : (k = 256)) (PreH6 : (cur = (Znth (i) (ptrs) (0)))) (PreH7 : (max = (Znth (best) (ptrs) (0)))) (PreH8 : (0 < words_size_pre)) (PreH9 : (words_size_pre < INT_MAX)) (PreH10 : ((Zlength (ptrs)) = words_size_pre)) (PreH11 : (problem_158_pre_z rows )) (PreH12 : (rows_well_formed_158 rows words_size_pre )) (PreH13 : (best_state_158 rows i best maxu )) ,
  (row_stores_missing_i_158 ptrs rows i )
|--
  “ (best < words_size_pre) ”
.

Definition find_max_entail_wit_5_split_goal_3 := 
forall (words_size_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (i: Z) (k: Z) (cur: Z) (max: Z) (best: Z) (maxu: Z) (retval: Z) (PreH1 : (retval = (string_length ((Znth (i) (rows) ((@nil Z))))))) (PreH2 : (0 <= ((string_length ((Znth (i) (rows) ((@nil Z))))) + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < words_size_pre)) (PreH5 : (k = 256)) (PreH6 : (cur = (Znth (i) (ptrs) (0)))) (PreH7 : (max = (Znth (best) (ptrs) (0)))) (PreH8 : (0 < words_size_pre)) (PreH9 : (words_size_pre < INT_MAX)) (PreH10 : ((Zlength (ptrs)) = words_size_pre)) (PreH11 : (problem_158_pre_z rows )) (PreH12 : (rows_well_formed_158 rows words_size_pre )) (PreH13 : (best_state_158 rows i best maxu )) ,
  (row_stores_missing_i_158 ptrs rows i )
|--
  “ (0 <= best) ”
.

Definition find_max_entail_wit_5_split_goal_4 := 
forall (words_size_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (i: Z) (k: Z) (cur: Z) (max: Z) (best: Z) (maxu: Z) (retval: Z) (PreH1 : (retval = (string_length ((Znth (i) (rows) ((@nil Z))))))) (PreH2 : (0 <= ((string_length ((Znth (i) (rows) ((@nil Z))))) + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < words_size_pre)) (PreH5 : (k = 256)) (PreH6 : (cur = (Znth (i) (ptrs) (0)))) (PreH7 : (max = (Znth (best) (ptrs) (0)))) (PreH8 : (0 < words_size_pre)) (PreH9 : (words_size_pre < INT_MAX)) (PreH10 : ((Zlength (ptrs)) = words_size_pre)) (PreH11 : (problem_158_pre_z rows )) (PreH12 : (rows_well_formed_158 rows words_size_pre )) (PreH13 : (best_state_158 rows i best maxu )) ,
  (row_stores_missing_i_158 ptrs rows i )
|--
  “ (0 <= retval) ”
.

Definition find_max_entail_wit_5_split_goal_spatial := 
forall (words_size_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (i: Z) (k: Z) (cur: Z) (max: Z) (best: Z) (maxu: Z) (retval: Z) (PreH1 : (retval = (string_length ((Znth (i) (rows) ((@nil Z))))))) (PreH2 : (0 <= ((string_length ((Znth (i) (rows) ((@nil Z))))) + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < words_size_pre)) (PreH5 : (k = 256)) (PreH6 : (cur = (Znth (i) (ptrs) (0)))) (PreH7 : (max = (Znth (best) (ptrs) (0)))) (PreH8 : (0 < words_size_pre)) (PreH9 : (words_size_pre < INT_MAX)) (PreH10 : ((Zlength (ptrs)) = words_size_pre)) (PreH11 : (problem_158_pre_z rows )) (PreH12 : (rows_well_formed_158 rows words_size_pre )) (PreH13 : (best_state_158 rows i best maxu )) ,
  (row_stores_missing_i_158 ptrs rows i )
|--
  (row_stores_missing_i_158 ptrs rows i )
.

Definition find_max_entail_wit_6 := 
(
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (seen_l_2: (@list Z)) (maxu: Z) (best: Z) (max: Z) (cur: Z) (k: Z) (unique: Z) (i: Z) (len: Z) (j: Z) (PreH1 : (j < len)) (PreH2 : (0 <= j)) (PreH3 : (j <= len)) (PreH4 : (len = (string_length ((Znth (i) (rows) ((@nil Z))))))) (PreH5 : (0 <= unique)) (PreH6 : (unique <= j)) (PreH7 : (k = 256)) (PreH8 : (0 <= i)) (PreH9 : (i < words_size_pre)) (PreH10 : (cur = (Znth (i) (ptrs) (0)))) (PreH11 : (max = (Znth (best) (ptrs) (0)))) (PreH12 : (0 <= best)) (PreH13 : (best < words_size_pre)) (PreH14 : (0 < words_size_pre)) (PreH15 : (words_size_pre < INT_MAX)) (PreH16 : ((Zlength (ptrs)) = words_size_pre)) (PreH17 : (problem_158_pre_z rows )) (PreH18 : (rows_well_formed_158 rows words_size_pre )) (PreH19 : (best_state_158 rows i best maxu )) (PreH20 : (seen_state_158 (Znth (i) (rows) ((@nil Z))) j seen_l_2 unique )) ,
  (PtrArray.full words_pre words_size_pre ptrs )
  **  (row_stores_missing_i_158 ptrs rows i )
  **  (store_string cur (Znth (i) (rows) ((@nil Z))) )
  **  (IntArray.full ( &( "seen" ) ) 256 seen_l_2 )
|--
  EX (seen_l: (@list Z)) ,
  “ (0 <= j) ” 
  &&  “ (j < len) ” 
  &&  “ (len = (string_length ((Znth (i) (rows) ((@nil Z)))))) ” 
  &&  “ (0 <= unique) ” 
  &&  “ (unique <= j) ” 
  &&  “ (0 <= (Znth j (c_string ((Znth (i) (rows) ((@nil Z))))) 0)) ” 
  &&  “ ((Znth j (c_string ((Znth (i) (rows) ((@nil Z))))) 0) < 256) ” 
  &&  “ ((Znth j (c_string ((Znth (i) (rows) ((@nil Z))))) 0) = (Znth (j) ((Znth (i) (rows) ((@nil Z)))) (0))) ” 
  &&  “ (k = 256) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < words_size_pre) ” 
  &&  “ (cur = (Znth (i) (ptrs) (0))) ” 
  &&  “ (max = (Znth (best) (ptrs) (0))) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best < words_size_pre) ” 
  &&  “ (0 < words_size_pre) ” 
  &&  “ (words_size_pre < INT_MAX) ” 
  &&  “ ((Zlength (ptrs)) = words_size_pre) ” 
  &&  “ (problem_158_pre_z rows ) ” 
  &&  “ (rows_well_formed_158 rows words_size_pre ) ” 
  &&  “ (best_state_158 rows i best maxu ) ” 
  &&  “ (seen_state_158 (Znth (i) (rows) ((@nil Z))) j seen_l unique ) ”
  &&  (PtrArray.full words_pre words_size_pre ptrs )
  **  (row_stores_missing_i_158 ptrs rows i )
  **  (store_string cur (Znth (i) (rows) ((@nil Z))) )
  **  (IntArray.full ( &( "seen" ) ) 256 seen_l )
) \/
(
forall (words_size_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (seen_l_2: (@list Z)) (maxu: Z) (best: Z) (max: Z) (cur: Z) (k: Z) (unique: Z) (i: Z) (len: Z) (j: Z) (PreH1 : (0 <= ((string_length ((Znth (i) (rows) ((@nil Z))))) + 1 ))) (PreH2 : (j < len)) (PreH3 : (0 <= j)) (PreH4 : (j <= len)) (PreH5 : (len = (string_length ((Znth (i) (rows) ((@nil Z))))))) (PreH6 : (0 <= unique)) (PreH7 : (unique <= j)) (PreH8 : (k = 256)) (PreH9 : (0 <= i)) (PreH10 : (i < words_size_pre)) (PreH11 : (cur = (Znth (i) (ptrs) (0)))) (PreH12 : (max = (Znth (best) (ptrs) (0)))) (PreH13 : (0 <= best)) (PreH14 : (best < words_size_pre)) (PreH15 : (0 < words_size_pre)) (PreH16 : (words_size_pre < INT_MAX)) (PreH17 : ((Zlength (ptrs)) = words_size_pre)) (PreH18 : (problem_158_pre_z rows )) (PreH19 : (rows_well_formed_158 rows words_size_pre )) (PreH20 : (best_state_158 rows i best maxu )) (PreH21 : (seen_state_158 (Znth (i) (rows) ((@nil Z))) j seen_l_2 unique )) ,
  (row_stores_missing_i_158 ptrs rows i )
|--
  “ ((Znth j (c_string ((Znth (i) (rows) ((@nil Z))))) 0) = (Znth (j) ((Znth (i) (rows) ((@nil Z)))) (0))) ” 
  &&  “ ((Znth j (c_string ((Znth (i) (rows) ((@nil Z))))) 0) < 256) ” 
  &&  “ (0 <= (Znth j (c_string ((Znth (i) (rows) ((@nil Z))))) 0)) ”
  &&  (row_stores_missing_i_158 ptrs rows i )
).

Definition find_max_entail_wit_6_split_goal_1 := 
forall (words_size_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (seen_l_2: (@list Z)) (maxu: Z) (best: Z) (max: Z) (cur: Z) (k: Z) (unique: Z) (i: Z) (len: Z) (j: Z) (PreH1 : (0 <= ((string_length ((Znth (i) (rows) ((@nil Z))))) + 1 ))) (PreH2 : (j < len)) (PreH3 : (0 <= j)) (PreH4 : (j <= len)) (PreH5 : (len = (string_length ((Znth (i) (rows) ((@nil Z))))))) (PreH6 : (0 <= unique)) (PreH7 : (unique <= j)) (PreH8 : (k = 256)) (PreH9 : (0 <= i)) (PreH10 : (i < words_size_pre)) (PreH11 : (cur = (Znth (i) (ptrs) (0)))) (PreH12 : (max = (Znth (best) (ptrs) (0)))) (PreH13 : (0 <= best)) (PreH14 : (best < words_size_pre)) (PreH15 : (0 < words_size_pre)) (PreH16 : (words_size_pre < INT_MAX)) (PreH17 : ((Zlength (ptrs)) = words_size_pre)) (PreH18 : (problem_158_pre_z rows )) (PreH19 : (rows_well_formed_158 rows words_size_pre )) (PreH20 : (best_state_158 rows i best maxu )) (PreH21 : (seen_state_158 (Znth (i) (rows) ((@nil Z))) j seen_l_2 unique )) ,
  (row_stores_missing_i_158 ptrs rows i )
|--
  “ ((Znth j (c_string ((Znth (i) (rows) ((@nil Z))))) 0) = (Znth (j) ((Znth (i) (rows) ((@nil Z)))) (0))) ”
.

Definition find_max_entail_wit_6_split_goal_2 := 
forall (words_size_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (seen_l_2: (@list Z)) (maxu: Z) (best: Z) (max: Z) (cur: Z) (k: Z) (unique: Z) (i: Z) (len: Z) (j: Z) (PreH1 : (0 <= ((string_length ((Znth (i) (rows) ((@nil Z))))) + 1 ))) (PreH2 : (j < len)) (PreH3 : (0 <= j)) (PreH4 : (j <= len)) (PreH5 : (len = (string_length ((Znth (i) (rows) ((@nil Z))))))) (PreH6 : (0 <= unique)) (PreH7 : (unique <= j)) (PreH8 : (k = 256)) (PreH9 : (0 <= i)) (PreH10 : (i < words_size_pre)) (PreH11 : (cur = (Znth (i) (ptrs) (0)))) (PreH12 : (max = (Znth (best) (ptrs) (0)))) (PreH13 : (0 <= best)) (PreH14 : (best < words_size_pre)) (PreH15 : (0 < words_size_pre)) (PreH16 : (words_size_pre < INT_MAX)) (PreH17 : ((Zlength (ptrs)) = words_size_pre)) (PreH18 : (problem_158_pre_z rows )) (PreH19 : (rows_well_formed_158 rows words_size_pre )) (PreH20 : (best_state_158 rows i best maxu )) (PreH21 : (seen_state_158 (Znth (i) (rows) ((@nil Z))) j seen_l_2 unique )) ,
  (row_stores_missing_i_158 ptrs rows i )
|--
  “ ((Znth j (c_string ((Znth (i) (rows) ((@nil Z))))) 0) < 256) ”
.

Definition find_max_entail_wit_6_split_goal_3 := 
forall (words_size_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (seen_l_2: (@list Z)) (maxu: Z) (best: Z) (max: Z) (cur: Z) (k: Z) (unique: Z) (i: Z) (len: Z) (j: Z) (PreH1 : (0 <= ((string_length ((Znth (i) (rows) ((@nil Z))))) + 1 ))) (PreH2 : (j < len)) (PreH3 : (0 <= j)) (PreH4 : (j <= len)) (PreH5 : (len = (string_length ((Znth (i) (rows) ((@nil Z))))))) (PreH6 : (0 <= unique)) (PreH7 : (unique <= j)) (PreH8 : (k = 256)) (PreH9 : (0 <= i)) (PreH10 : (i < words_size_pre)) (PreH11 : (cur = (Znth (i) (ptrs) (0)))) (PreH12 : (max = (Znth (best) (ptrs) (0)))) (PreH13 : (0 <= best)) (PreH14 : (best < words_size_pre)) (PreH15 : (0 < words_size_pre)) (PreH16 : (words_size_pre < INT_MAX)) (PreH17 : ((Zlength (ptrs)) = words_size_pre)) (PreH18 : (problem_158_pre_z rows )) (PreH19 : (rows_well_formed_158 rows words_size_pre )) (PreH20 : (best_state_158 rows i best maxu )) (PreH21 : (seen_state_158 (Znth (i) (rows) ((@nil Z))) j seen_l_2 unique )) ,
  (row_stores_missing_i_158 ptrs rows i )
|--
  “ (0 <= (Znth j (c_string ((Znth (i) (rows) ((@nil Z))))) 0)) ”
.

Definition find_max_entail_wit_6_split_goal_spatial := 
forall (words_size_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (seen_l_2: (@list Z)) (maxu: Z) (best: Z) (max: Z) (cur: Z) (k: Z) (unique: Z) (i: Z) (len: Z) (j: Z) (PreH1 : (0 <= ((string_length ((Znth (i) (rows) ((@nil Z))))) + 1 ))) (PreH2 : (j < len)) (PreH3 : (0 <= j)) (PreH4 : (j <= len)) (PreH5 : (len = (string_length ((Znth (i) (rows) ((@nil Z))))))) (PreH6 : (0 <= unique)) (PreH7 : (unique <= j)) (PreH8 : (k = 256)) (PreH9 : (0 <= i)) (PreH10 : (i < words_size_pre)) (PreH11 : (cur = (Znth (i) (ptrs) (0)))) (PreH12 : (max = (Znth (best) (ptrs) (0)))) (PreH13 : (0 <= best)) (PreH14 : (best < words_size_pre)) (PreH15 : (0 < words_size_pre)) (PreH16 : (words_size_pre < INT_MAX)) (PreH17 : ((Zlength (ptrs)) = words_size_pre)) (PreH18 : (problem_158_pre_z rows )) (PreH19 : (rows_well_formed_158 rows words_size_pre )) (PreH20 : (best_state_158 rows i best maxu )) (PreH21 : (seen_state_158 (Znth (i) (rows) ((@nil Z))) j seen_l_2 unique )) ,
  (row_stores_missing_i_158 ptrs rows i )
|--
  (row_stores_missing_i_158 ptrs rows i )
.

Definition find_max_entail_wit_7_1 := 
(
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (seen_l_2: (@list Z)) (j: Z) (len: Z) (i: Z) (unique: Z) (ch: Z) (k: Z) (cur: Z) (max: Z) (best: Z) (maxu: Z) (PreH1 : ((Znth ch seen_l_2 0) = 0)) (PreH2 : (0 <= ((string_length ((Znth (i) (rows) ((@nil Z))))) + 1 ))) (PreH3 : (0 <= j)) (PreH4 : (j < len)) (PreH5 : (len = (string_length ((Znth (i) (rows) ((@nil Z))))))) (PreH6 : (0 <= unique)) (PreH7 : (unique <= j)) (PreH8 : (0 <= ch)) (PreH9 : (ch < 256)) (PreH10 : (ch = (Znth (j) ((Znth (i) (rows) ((@nil Z)))) (0)))) (PreH11 : (k = 256)) (PreH12 : (0 <= i)) (PreH13 : (i < words_size_pre)) (PreH14 : (cur = (Znth (i) (ptrs) (0)))) (PreH15 : (max = (Znth (best) (ptrs) (0)))) (PreH16 : (0 <= best)) (PreH17 : (best < words_size_pre)) (PreH18 : (0 < words_size_pre)) (PreH19 : (words_size_pre < INT_MAX)) (PreH20 : ((Zlength (ptrs)) = words_size_pre)) (PreH21 : (problem_158_pre_z rows )) (PreH22 : (rows_well_formed_158 rows words_size_pre )) (PreH23 : (best_state_158 rows i best maxu )) (PreH24 : (seen_state_158 (Znth (i) (rows) ((@nil Z))) j seen_l_2 unique )) ,
  (IntArray.full ( &( "seen" ) ) 256 (replace_Znth (ch) (1) (seen_l_2)) )
  **  (CharArray.full cur ((string_length ((Znth (i) (rows) ((@nil Z))))) + 1 ) (c_string ((Znth (i) (rows) ((@nil Z))))) )
  **  (PtrArray.full words_pre words_size_pre ptrs )
  **  (row_stores_missing_i_158 ptrs rows i )
|--
  EX (seen_l: (@list Z)) ,
  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= len) ” 
  &&  “ (len = (string_length ((Znth (i) (rows) ((@nil Z)))))) ” 
  &&  “ (0 <= (unique + 1 )) ” 
  &&  “ ((unique + 1 ) <= (j + 1 )) ” 
  &&  “ (k = 256) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < words_size_pre) ” 
  &&  “ (cur = (Znth (i) (ptrs) (0))) ” 
  &&  “ (max = (Znth (best) (ptrs) (0))) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best < words_size_pre) ” 
  &&  “ (0 < words_size_pre) ” 
  &&  “ (words_size_pre < INT_MAX) ” 
  &&  “ ((Zlength (ptrs)) = words_size_pre) ” 
  &&  “ (problem_158_pre_z rows ) ” 
  &&  “ (rows_well_formed_158 rows words_size_pre ) ” 
  &&  “ (best_state_158 rows i best maxu ) ” 
  &&  “ (seen_state_158 (Znth (i) (rows) ((@nil Z))) (j + 1 ) seen_l (unique + 1 ) ) ”
  &&  (PtrArray.full words_pre words_size_pre ptrs )
  **  (row_stores_missing_i_158 ptrs rows i )
  **  (store_string cur (Znth (i) (rows) ((@nil Z))) )
  **  (IntArray.full ( &( "seen" ) ) 256 seen_l )
) \/
(
forall (words_size_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (seen_l_2: (@list Z)) (j: Z) (len: Z) (i: Z) (unique: Z) (ch: Z) (k: Z) (cur: Z) (max: Z) (best: Z) (maxu: Z) (PreH1 : ((Znth ch seen_l_2 0) = 0)) (PreH2 : (0 <= ((string_length ((Znth (i) (rows) ((@nil Z))))) + 1 ))) (PreH3 : (0 <= j)) (PreH4 : (j < len)) (PreH5 : (len = (string_length ((Znth (i) (rows) ((@nil Z))))))) (PreH6 : (0 <= unique)) (PreH7 : (unique <= j)) (PreH8 : (0 <= ch)) (PreH9 : (ch < 256)) (PreH10 : (ch = (Znth (j) ((Znth (i) (rows) ((@nil Z)))) (0)))) (PreH11 : (k = 256)) (PreH12 : (0 <= i)) (PreH13 : (i < words_size_pre)) (PreH14 : (cur = (Znth (i) (ptrs) (0)))) (PreH15 : (max = (Znth (best) (ptrs) (0)))) (PreH16 : (0 <= best)) (PreH17 : (best < words_size_pre)) (PreH18 : (0 < words_size_pre)) (PreH19 : (words_size_pre < INT_MAX)) (PreH20 : ((Zlength (ptrs)) = words_size_pre)) (PreH21 : (problem_158_pre_z rows )) (PreH22 : (rows_well_formed_158 rows words_size_pre )) (PreH23 : (best_state_158 rows i best maxu )) (PreH24 : (seen_state_158 (Znth (i) (rows) ((@nil Z))) j seen_l_2 unique )) ,
  (row_stores_missing_i_158 ptrs rows i )
|--
  “ (seen_state_158 (Znth (i) (rows) ((@nil Z))) (j + 1 ) (replace_Znth (ch) (1) (seen_l_2)) (unique + 1 ) ) ”
  &&  (row_stores_missing_i_158 ptrs rows i )
).

Definition find_max_entail_wit_7_1_split_goal_1 := 
forall (words_size_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (seen_l_2: (@list Z)) (j: Z) (len: Z) (i: Z) (unique: Z) (ch: Z) (k: Z) (cur: Z) (max: Z) (best: Z) (maxu: Z) (PreH1 : ((Znth ch seen_l_2 0) = 0)) (PreH2 : (0 <= ((string_length ((Znth (i) (rows) ((@nil Z))))) + 1 ))) (PreH3 : (0 <= j)) (PreH4 : (j < len)) (PreH5 : (len = (string_length ((Znth (i) (rows) ((@nil Z))))))) (PreH6 : (0 <= unique)) (PreH7 : (unique <= j)) (PreH8 : (0 <= ch)) (PreH9 : (ch < 256)) (PreH10 : (ch = (Znth (j) ((Znth (i) (rows) ((@nil Z)))) (0)))) (PreH11 : (k = 256)) (PreH12 : (0 <= i)) (PreH13 : (i < words_size_pre)) (PreH14 : (cur = (Znth (i) (ptrs) (0)))) (PreH15 : (max = (Znth (best) (ptrs) (0)))) (PreH16 : (0 <= best)) (PreH17 : (best < words_size_pre)) (PreH18 : (0 < words_size_pre)) (PreH19 : (words_size_pre < INT_MAX)) (PreH20 : ((Zlength (ptrs)) = words_size_pre)) (PreH21 : (problem_158_pre_z rows )) (PreH22 : (rows_well_formed_158 rows words_size_pre )) (PreH23 : (best_state_158 rows i best maxu )) (PreH24 : (seen_state_158 (Znth (i) (rows) ((@nil Z))) j seen_l_2 unique )) ,
  (row_stores_missing_i_158 ptrs rows i )
|--
  “ (seen_state_158 (Znth (i) (rows) ((@nil Z))) (j + 1 ) (replace_Znth (ch) (1) (seen_l_2)) (unique + 1 ) ) ”
.

Definition find_max_entail_wit_7_1_split_goal_spatial := 
forall (words_size_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (seen_l_2: (@list Z)) (j: Z) (len: Z) (i: Z) (unique: Z) (ch: Z) (k: Z) (cur: Z) (max: Z) (best: Z) (maxu: Z) (PreH1 : ((Znth ch seen_l_2 0) = 0)) (PreH2 : (0 <= ((string_length ((Znth (i) (rows) ((@nil Z))))) + 1 ))) (PreH3 : (0 <= j)) (PreH4 : (j < len)) (PreH5 : (len = (string_length ((Znth (i) (rows) ((@nil Z))))))) (PreH6 : (0 <= unique)) (PreH7 : (unique <= j)) (PreH8 : (0 <= ch)) (PreH9 : (ch < 256)) (PreH10 : (ch = (Znth (j) ((Znth (i) (rows) ((@nil Z)))) (0)))) (PreH11 : (k = 256)) (PreH12 : (0 <= i)) (PreH13 : (i < words_size_pre)) (PreH14 : (cur = (Znth (i) (ptrs) (0)))) (PreH15 : (max = (Znth (best) (ptrs) (0)))) (PreH16 : (0 <= best)) (PreH17 : (best < words_size_pre)) (PreH18 : (0 < words_size_pre)) (PreH19 : (words_size_pre < INT_MAX)) (PreH20 : ((Zlength (ptrs)) = words_size_pre)) (PreH21 : (problem_158_pre_z rows )) (PreH22 : (rows_well_formed_158 rows words_size_pre )) (PreH23 : (best_state_158 rows i best maxu )) (PreH24 : (seen_state_158 (Znth (i) (rows) ((@nil Z))) j seen_l_2 unique )) ,
  (row_stores_missing_i_158 ptrs rows i )
|--
  (row_stores_missing_i_158 ptrs rows i )
.

Definition find_max_entail_wit_7_2 := 
(
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (seen_l_2: (@list Z)) (j: Z) (len: Z) (i: Z) (unique: Z) (ch: Z) (k: Z) (cur: Z) (max: Z) (best: Z) (maxu: Z) (PreH1 : ((Znth ch seen_l_2 0) <> 0)) (PreH2 : (0 <= ((string_length ((Znth (i) (rows) ((@nil Z))))) + 1 ))) (PreH3 : (0 <= j)) (PreH4 : (j < len)) (PreH5 : (len = (string_length ((Znth (i) (rows) ((@nil Z))))))) (PreH6 : (0 <= unique)) (PreH7 : (unique <= j)) (PreH8 : (0 <= ch)) (PreH9 : (ch < 256)) (PreH10 : (ch = (Znth (j) ((Znth (i) (rows) ((@nil Z)))) (0)))) (PreH11 : (k = 256)) (PreH12 : (0 <= i)) (PreH13 : (i < words_size_pre)) (PreH14 : (cur = (Znth (i) (ptrs) (0)))) (PreH15 : (max = (Znth (best) (ptrs) (0)))) (PreH16 : (0 <= best)) (PreH17 : (best < words_size_pre)) (PreH18 : (0 < words_size_pre)) (PreH19 : (words_size_pre < INT_MAX)) (PreH20 : ((Zlength (ptrs)) = words_size_pre)) (PreH21 : (problem_158_pre_z rows )) (PreH22 : (rows_well_formed_158 rows words_size_pre )) (PreH23 : (best_state_158 rows i best maxu )) (PreH24 : (seen_state_158 (Znth (i) (rows) ((@nil Z))) j seen_l_2 unique )) ,
  (IntArray.full ( &( "seen" ) ) 256 seen_l_2 )
  **  (CharArray.full cur ((string_length ((Znth (i) (rows) ((@nil Z))))) + 1 ) (c_string ((Znth (i) (rows) ((@nil Z))))) )
  **  (PtrArray.full words_pre words_size_pre ptrs )
  **  (row_stores_missing_i_158 ptrs rows i )
|--
  EX (seen_l: (@list Z)) ,
  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= len) ” 
  &&  “ (len = (string_length ((Znth (i) (rows) ((@nil Z)))))) ” 
  &&  “ (0 <= unique) ” 
  &&  “ (unique <= (j + 1 )) ” 
  &&  “ (k = 256) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < words_size_pre) ” 
  &&  “ (cur = (Znth (i) (ptrs) (0))) ” 
  &&  “ (max = (Znth (best) (ptrs) (0))) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best < words_size_pre) ” 
  &&  “ (0 < words_size_pre) ” 
  &&  “ (words_size_pre < INT_MAX) ” 
  &&  “ ((Zlength (ptrs)) = words_size_pre) ” 
  &&  “ (problem_158_pre_z rows ) ” 
  &&  “ (rows_well_formed_158 rows words_size_pre ) ” 
  &&  “ (best_state_158 rows i best maxu ) ” 
  &&  “ (seen_state_158 (Znth (i) (rows) ((@nil Z))) (j + 1 ) seen_l unique ) ”
  &&  (PtrArray.full words_pre words_size_pre ptrs )
  **  (row_stores_missing_i_158 ptrs rows i )
  **  (store_string cur (Znth (i) (rows) ((@nil Z))) )
  **  (IntArray.full ( &( "seen" ) ) 256 seen_l )
) \/
(
forall (words_size_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (seen_l_2: (@list Z)) (j: Z) (len: Z) (i: Z) (unique: Z) (ch: Z) (k: Z) (cur: Z) (max: Z) (best: Z) (maxu: Z) (PreH1 : ((Znth ch seen_l_2 0) <> 0)) (PreH2 : (0 <= ((string_length ((Znth (i) (rows) ((@nil Z))))) + 1 ))) (PreH3 : (0 <= j)) (PreH4 : (j < len)) (PreH5 : (len = (string_length ((Znth (i) (rows) ((@nil Z))))))) (PreH6 : (0 <= unique)) (PreH7 : (unique <= j)) (PreH8 : (0 <= ch)) (PreH9 : (ch < 256)) (PreH10 : (ch = (Znth (j) ((Znth (i) (rows) ((@nil Z)))) (0)))) (PreH11 : (k = 256)) (PreH12 : (0 <= i)) (PreH13 : (i < words_size_pre)) (PreH14 : (cur = (Znth (i) (ptrs) (0)))) (PreH15 : (max = (Znth (best) (ptrs) (0)))) (PreH16 : (0 <= best)) (PreH17 : (best < words_size_pre)) (PreH18 : (0 < words_size_pre)) (PreH19 : (words_size_pre < INT_MAX)) (PreH20 : ((Zlength (ptrs)) = words_size_pre)) (PreH21 : (problem_158_pre_z rows )) (PreH22 : (rows_well_formed_158 rows words_size_pre )) (PreH23 : (best_state_158 rows i best maxu )) (PreH24 : (seen_state_158 (Znth (i) (rows) ((@nil Z))) j seen_l_2 unique )) ,
  (row_stores_missing_i_158 ptrs rows i )
|--
  “ (seen_state_158 (Znth (i) (rows) ((@nil Z))) (j + 1 ) seen_l_2 unique ) ”
  &&  (row_stores_missing_i_158 ptrs rows i )
).

Definition find_max_entail_wit_7_2_split_goal_1 := 
forall (words_size_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (seen_l_2: (@list Z)) (j: Z) (len: Z) (i: Z) (unique: Z) (ch: Z) (k: Z) (cur: Z) (max: Z) (best: Z) (maxu: Z) (PreH1 : ((Znth ch seen_l_2 0) <> 0)) (PreH2 : (0 <= ((string_length ((Znth (i) (rows) ((@nil Z))))) + 1 ))) (PreH3 : (0 <= j)) (PreH4 : (j < len)) (PreH5 : (len = (string_length ((Znth (i) (rows) ((@nil Z))))))) (PreH6 : (0 <= unique)) (PreH7 : (unique <= j)) (PreH8 : (0 <= ch)) (PreH9 : (ch < 256)) (PreH10 : (ch = (Znth (j) ((Znth (i) (rows) ((@nil Z)))) (0)))) (PreH11 : (k = 256)) (PreH12 : (0 <= i)) (PreH13 : (i < words_size_pre)) (PreH14 : (cur = (Znth (i) (ptrs) (0)))) (PreH15 : (max = (Znth (best) (ptrs) (0)))) (PreH16 : (0 <= best)) (PreH17 : (best < words_size_pre)) (PreH18 : (0 < words_size_pre)) (PreH19 : (words_size_pre < INT_MAX)) (PreH20 : ((Zlength (ptrs)) = words_size_pre)) (PreH21 : (problem_158_pre_z rows )) (PreH22 : (rows_well_formed_158 rows words_size_pre )) (PreH23 : (best_state_158 rows i best maxu )) (PreH24 : (seen_state_158 (Znth (i) (rows) ((@nil Z))) j seen_l_2 unique )) ,
  (row_stores_missing_i_158 ptrs rows i )
|--
  “ (seen_state_158 (Znth (i) (rows) ((@nil Z))) (j + 1 ) seen_l_2 unique ) ”
.

Definition find_max_entail_wit_7_2_split_goal_spatial := 
forall (words_size_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (seen_l_2: (@list Z)) (j: Z) (len: Z) (i: Z) (unique: Z) (ch: Z) (k: Z) (cur: Z) (max: Z) (best: Z) (maxu: Z) (PreH1 : ((Znth ch seen_l_2 0) <> 0)) (PreH2 : (0 <= ((string_length ((Znth (i) (rows) ((@nil Z))))) + 1 ))) (PreH3 : (0 <= j)) (PreH4 : (j < len)) (PreH5 : (len = (string_length ((Znth (i) (rows) ((@nil Z))))))) (PreH6 : (0 <= unique)) (PreH7 : (unique <= j)) (PreH8 : (0 <= ch)) (PreH9 : (ch < 256)) (PreH10 : (ch = (Znth (j) ((Znth (i) (rows) ((@nil Z)))) (0)))) (PreH11 : (k = 256)) (PreH12 : (0 <= i)) (PreH13 : (i < words_size_pre)) (PreH14 : (cur = (Znth (i) (ptrs) (0)))) (PreH15 : (max = (Znth (best) (ptrs) (0)))) (PreH16 : (0 <= best)) (PreH17 : (best < words_size_pre)) (PreH18 : (0 < words_size_pre)) (PreH19 : (words_size_pre < INT_MAX)) (PreH20 : ((Zlength (ptrs)) = words_size_pre)) (PreH21 : (problem_158_pre_z rows )) (PreH22 : (rows_well_formed_158 rows words_size_pre )) (PreH23 : (best_state_158 rows i best maxu )) (PreH24 : (seen_state_158 (Znth (i) (rows) ((@nil Z))) j seen_l_2 unique )) ,
  (row_stores_missing_i_158 ptrs rows i )
|--
  (row_stores_missing_i_158 ptrs rows i )
.

Definition find_max_entail_wit_8 := 
(
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (seen_l_2: (@list Z)) (maxu: Z) (best: Z) (max: Z) (cur: Z) (k: Z) (unique: Z) (i: Z) (len: Z) (j: Z) (PreH1 : (j >= len)) (PreH2 : (0 <= j)) (PreH3 : (j <= len)) (PreH4 : (len = (string_length ((Znth (i) (rows) ((@nil Z))))))) (PreH5 : (0 <= unique)) (PreH6 : (unique <= j)) (PreH7 : (k = 256)) (PreH8 : (0 <= i)) (PreH9 : (i < words_size_pre)) (PreH10 : (cur = (Znth (i) (ptrs) (0)))) (PreH11 : (max = (Znth (best) (ptrs) (0)))) (PreH12 : (0 <= best)) (PreH13 : (best < words_size_pre)) (PreH14 : (0 < words_size_pre)) (PreH15 : (words_size_pre < INT_MAX)) (PreH16 : ((Zlength (ptrs)) = words_size_pre)) (PreH17 : (problem_158_pre_z rows )) (PreH18 : (rows_well_formed_158 rows words_size_pre )) (PreH19 : (best_state_158 rows i best maxu )) (PreH20 : (seen_state_158 (Znth (i) (rows) ((@nil Z))) j seen_l_2 unique )) ,
  (PtrArray.full words_pre words_size_pre ptrs )
  **  (row_stores_missing_i_158 ptrs rows i )
  **  (store_string cur (Znth (i) (rows) ((@nil Z))) )
  **  (IntArray.full ( &( "seen" ) ) 256 seen_l_2 )
|--
  EX (seen_l: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i < words_size_pre) ” 
  &&  “ (j = len) ” 
  &&  “ (k = 256) ” 
  &&  “ (cur = (Znth (i) (ptrs) (0))) ” 
  &&  “ (max = (Znth (best) (ptrs) (0))) ” 
  &&  “ (unique = (unique_count_z_158 ((Znth (i) (rows) ((@nil Z)))))) ” 
  &&  “ (0 < words_size_pre) ” 
  &&  “ (words_size_pre < INT_MAX) ” 
  &&  “ ((Zlength (ptrs)) = words_size_pre) ” 
  &&  “ (problem_158_pre_z rows ) ” 
  &&  “ (rows_well_formed_158 rows words_size_pre ) ” 
  &&  “ (best_state_158 rows i best maxu ) ”
  &&  (PtrArray.full words_pre words_size_pre ptrs )
  **  (row_stores_158 ptrs rows )
  **  (IntArray.full ( &( "seen" ) ) 256 seen_l )
) \/
(
forall (words_size_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (seen_l_2: (@list Z)) (maxu: Z) (best: Z) (max: Z) (cur: Z) (k: Z) (unique: Z) (i: Z) (len: Z) (j: Z) (PreH1 : (0 <= ((string_length ((Znth (i) (rows) ((@nil Z))))) + 1 ))) (PreH2 : (j >= len)) (PreH3 : (0 <= j)) (PreH4 : (j <= len)) (PreH5 : (len = (string_length ((Znth (i) (rows) ((@nil Z))))))) (PreH6 : (0 <= unique)) (PreH7 : (unique <= j)) (PreH8 : (k = 256)) (PreH9 : (0 <= i)) (PreH10 : (i < words_size_pre)) (PreH11 : (cur = (Znth (i) (ptrs) (0)))) (PreH12 : (max = (Znth (best) (ptrs) (0)))) (PreH13 : (0 <= best)) (PreH14 : (best < words_size_pre)) (PreH15 : (0 < words_size_pre)) (PreH16 : (words_size_pre < INT_MAX)) (PreH17 : ((Zlength (ptrs)) = words_size_pre)) (PreH18 : (problem_158_pre_z rows )) (PreH19 : (rows_well_formed_158 rows words_size_pre )) (PreH20 : (best_state_158 rows i best maxu )) (PreH21 : (seen_state_158 (Znth (i) (rows) ((@nil Z))) j seen_l_2 unique )) ,
  (CharArray.full cur ((string_length ((Znth (i) (rows) ((@nil Z))))) + 1 ) (c_string ((Znth (i) (rows) ((@nil Z))))) )
  **  (row_stores_missing_i_158 ptrs rows i )
|--
  “ (unique = (unique_count_z_158 ((Znth (i) (rows) ((@nil Z)))))) ”
  &&  (row_stores_158 ptrs rows )
).

Definition find_max_entail_wit_8_split_goal_1 := 
forall (words_size_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (seen_l_2: (@list Z)) (maxu: Z) (best: Z) (max: Z) (cur: Z) (k: Z) (unique: Z) (i: Z) (len: Z) (j: Z) (PreH1 : (0 <= ((string_length ((Znth (i) (rows) ((@nil Z))))) + 1 ))) (PreH2 : (j >= len)) (PreH3 : (0 <= j)) (PreH4 : (j <= len)) (PreH5 : (len = (string_length ((Znth (i) (rows) ((@nil Z))))))) (PreH6 : (0 <= unique)) (PreH7 : (unique <= j)) (PreH8 : (k = 256)) (PreH9 : (0 <= i)) (PreH10 : (i < words_size_pre)) (PreH11 : (cur = (Znth (i) (ptrs) (0)))) (PreH12 : (max = (Znth (best) (ptrs) (0)))) (PreH13 : (0 <= best)) (PreH14 : (best < words_size_pre)) (PreH15 : (0 < words_size_pre)) (PreH16 : (words_size_pre < INT_MAX)) (PreH17 : ((Zlength (ptrs)) = words_size_pre)) (PreH18 : (problem_158_pre_z rows )) (PreH19 : (rows_well_formed_158 rows words_size_pre )) (PreH20 : (best_state_158 rows i best maxu )) (PreH21 : (seen_state_158 (Znth (i) (rows) ((@nil Z))) j seen_l_2 unique )) ,
  (CharArray.full cur ((string_length ((Znth (i) (rows) ((@nil Z))))) + 1 ) (c_string ((Znth (i) (rows) ((@nil Z))))) )
  **  (row_stores_missing_i_158 ptrs rows i )
|--
  “ (unique = (unique_count_z_158 ((Znth (i) (rows) ((@nil Z)))))) ”
.

Definition find_max_entail_wit_8_split_goal_spatial := 
forall (words_size_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (seen_l_2: (@list Z)) (maxu: Z) (best: Z) (max: Z) (cur: Z) (k: Z) (unique: Z) (i: Z) (len: Z) (j: Z) (PreH1 : (0 <= ((string_length ((Znth (i) (rows) ((@nil Z))))) + 1 ))) (PreH2 : (j >= len)) (PreH3 : (0 <= j)) (PreH4 : (j <= len)) (PreH5 : (len = (string_length ((Znth (i) (rows) ((@nil Z))))))) (PreH6 : (0 <= unique)) (PreH7 : (unique <= j)) (PreH8 : (k = 256)) (PreH9 : (0 <= i)) (PreH10 : (i < words_size_pre)) (PreH11 : (cur = (Znth (i) (ptrs) (0)))) (PreH12 : (max = (Znth (best) (ptrs) (0)))) (PreH13 : (0 <= best)) (PreH14 : (best < words_size_pre)) (PreH15 : (0 < words_size_pre)) (PreH16 : (words_size_pre < INT_MAX)) (PreH17 : ((Zlength (ptrs)) = words_size_pre)) (PreH18 : (problem_158_pre_z rows )) (PreH19 : (rows_well_formed_158 rows words_size_pre )) (PreH20 : (best_state_158 rows i best maxu )) (PreH21 : (seen_state_158 (Znth (i) (rows) ((@nil Z))) j seen_l_2 unique )) ,
  (CharArray.full cur ((string_length ((Znth (i) (rows) ((@nil Z))))) + 1 ) (c_string ((Znth (i) (rows) ((@nil Z))))) )
  **  (row_stores_missing_i_158 ptrs rows i )
|--
  (row_stores_158 ptrs rows )
.

Definition find_max_entail_wit_9 := 
(
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (seen_l_2: (@list Z)) (i: Z) (j: Z) (len: Z) (k: Z) (cur: Z) (max: Z) (best: Z) (unique: Z) (maxu: Z) (PreH1 : (i <> best)) (PreH2 : (unique = maxu)) (PreH3 : (unique <= maxu)) (PreH4 : (0 <= i)) (PreH5 : (i < words_size_pre)) (PreH6 : (j = len)) (PreH7 : (k = 256)) (PreH8 : (cur = (Znth (i) (ptrs) (0)))) (PreH9 : (max = (Znth (best) (ptrs) (0)))) (PreH10 : (unique = (unique_count_z_158 ((Znth (i) (rows) ((@nil Z))))))) (PreH11 : (0 < words_size_pre)) (PreH12 : (words_size_pre < INT_MAX)) (PreH13 : ((Zlength (ptrs)) = words_size_pre)) (PreH14 : (problem_158_pre_z rows )) (PreH15 : (rows_well_formed_158 rows words_size_pre )) (PreH16 : (best_state_158 rows i best maxu )) ,
  (PtrArray.full words_pre words_size_pre ptrs )
  **  (row_stores_158 ptrs rows )
  **  (IntArray.full ( &( "seen" ) ) 256 seen_l_2 )
|--
  EX (seen_l: (@list Z)) ,
  “ (0 <= best) ” 
  &&  “ (best < i) ” 
  &&  “ (i < words_size_pre) ” 
  &&  “ (j = len) ” 
  &&  “ (k = 256) ” 
  &&  “ (cur = (Znth (i) (ptrs) (0))) ” 
  &&  “ (max = (Znth (best) (ptrs) (0))) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (unique = (unique_count_z_158 ((Znth (i) (rows) ((@nil Z)))))) ” 
  &&  “ (unique = maxu) ” 
  &&  “ (0 < words_size_pre) ” 
  &&  “ (words_size_pre < INT_MAX) ” 
  &&  “ ((Zlength (ptrs)) = words_size_pre) ” 
  &&  “ (problem_158_pre_z rows ) ” 
  &&  “ (rows_well_formed_158 rows words_size_pre ) ” 
  &&  “ (best_state_158 rows i best maxu ) ”
  &&  (PtrArray.full words_pre words_size_pre ptrs )
  **  (row_stores_missing_two_158 ptrs rows best i )
  **  (store_string max (Znth (best) (rows) ((@nil Z))) )
  **  (store_string cur (Znth (i) (rows) ((@nil Z))) )
  **  (IntArray.full ( &( "seen" ) ) 256 seen_l )
) \/
(
forall (words_size_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (i: Z) (j: Z) (len: Z) (k: Z) (cur: Z) (max: Z) (best: Z) (unique: Z) (maxu: Z) (PreH1 : (i <> best)) (PreH2 : (unique = maxu)) (PreH3 : (unique <= maxu)) (PreH4 : (0 <= i)) (PreH5 : (i < words_size_pre)) (PreH6 : (j = len)) (PreH7 : (k = 256)) (PreH8 : (cur = (Znth (i) (ptrs) (0)))) (PreH9 : (max = (Znth (best) (ptrs) (0)))) (PreH10 : (unique = (unique_count_z_158 ((Znth (i) (rows) ((@nil Z))))))) (PreH11 : (0 < words_size_pre)) (PreH12 : (words_size_pre < INT_MAX)) (PreH13 : ((Zlength (ptrs)) = words_size_pre)) (PreH14 : (problem_158_pre_z rows )) (PreH15 : (rows_well_formed_158 rows words_size_pre )) (PreH16 : (best_state_158 rows i best maxu )) ,
  (row_stores_158 ptrs rows )
|--
  “ (best < i) ” 
  &&  “ (0 <= best) ”
  &&  (CharArray.full cur ((string_length ((Znth (i) (rows) ((@nil Z))))) + 1 ) (c_string ((Znth (i) (rows) ((@nil Z))))) )
  **  (CharArray.full max ((string_length ((Znth (best) (rows) ((@nil Z))))) + 1 ) (c_string ((Znth (best) (rows) ((@nil Z))))) )
  **  (row_stores_missing_two_158 ptrs rows best i )
).

Definition find_max_entail_wit_9_split_goal_1 := 
forall (words_size_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (i: Z) (j: Z) (len: Z) (k: Z) (cur: Z) (max: Z) (best: Z) (unique: Z) (maxu: Z) (PreH1 : (i <> best)) (PreH2 : (unique = maxu)) (PreH3 : (unique <= maxu)) (PreH4 : (0 <= i)) (PreH5 : (i < words_size_pre)) (PreH6 : (j = len)) (PreH7 : (k = 256)) (PreH8 : (cur = (Znth (i) (ptrs) (0)))) (PreH9 : (max = (Znth (best) (ptrs) (0)))) (PreH10 : (unique = (unique_count_z_158 ((Znth (i) (rows) ((@nil Z))))))) (PreH11 : (0 < words_size_pre)) (PreH12 : (words_size_pre < INT_MAX)) (PreH13 : ((Zlength (ptrs)) = words_size_pre)) (PreH14 : (problem_158_pre_z rows )) (PreH15 : (rows_well_formed_158 rows words_size_pre )) (PreH16 : (best_state_158 rows i best maxu )) ,
  (row_stores_158 ptrs rows )
|--
  “ (best < i) ”
.

Definition find_max_entail_wit_9_split_goal_2 := 
forall (words_size_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (i: Z) (j: Z) (len: Z) (k: Z) (cur: Z) (max: Z) (best: Z) (unique: Z) (maxu: Z) (PreH1 : (i <> best)) (PreH2 : (unique = maxu)) (PreH3 : (unique <= maxu)) (PreH4 : (0 <= i)) (PreH5 : (i < words_size_pre)) (PreH6 : (j = len)) (PreH7 : (k = 256)) (PreH8 : (cur = (Znth (i) (ptrs) (0)))) (PreH9 : (max = (Znth (best) (ptrs) (0)))) (PreH10 : (unique = (unique_count_z_158 ((Znth (i) (rows) ((@nil Z))))))) (PreH11 : (0 < words_size_pre)) (PreH12 : (words_size_pre < INT_MAX)) (PreH13 : ((Zlength (ptrs)) = words_size_pre)) (PreH14 : (problem_158_pre_z rows )) (PreH15 : (rows_well_formed_158 rows words_size_pre )) (PreH16 : (best_state_158 rows i best maxu )) ,
  (row_stores_158 ptrs rows )
|--
  “ (0 <= best) ”
.

Definition find_max_entail_wit_9_split_goal_spatial := 
forall (words_size_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (i: Z) (j: Z) (len: Z) (k: Z) (cur: Z) (max: Z) (best: Z) (unique: Z) (maxu: Z) (PreH1 : (i <> best)) (PreH2 : (unique = maxu)) (PreH3 : (unique <= maxu)) (PreH4 : (0 <= i)) (PreH5 : (i < words_size_pre)) (PreH6 : (j = len)) (PreH7 : (k = 256)) (PreH8 : (cur = (Znth (i) (ptrs) (0)))) (PreH9 : (max = (Znth (best) (ptrs) (0)))) (PreH10 : (unique = (unique_count_z_158 ((Znth (i) (rows) ((@nil Z))))))) (PreH11 : (0 < words_size_pre)) (PreH12 : (words_size_pre < INT_MAX)) (PreH13 : ((Zlength (ptrs)) = words_size_pre)) (PreH14 : (problem_158_pre_z rows )) (PreH15 : (rows_well_formed_158 rows words_size_pre )) (PreH16 : (best_state_158 rows i best maxu )) ,
  (row_stores_158 ptrs rows )
|--
  (CharArray.full cur ((string_length ((Znth (i) (rows) ((@nil Z))))) + 1 ) (c_string ((Znth (i) (rows) ((@nil Z))))) )
  **  (CharArray.full max ((string_length ((Znth (best) (rows) ((@nil Z))))) + 1 ) (c_string ((Znth (best) (rows) ((@nil Z))))) )
  **  (row_stores_missing_two_158 ptrs rows best i )
.

Definition find_max_entail_wit_10 := 
(
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (seen_l_2: (@list Z)) (best: Z) (i: Z) (j: Z) (len: Z) (k: Z) (cur: Z) (max: Z) (better: Z) (cmp: Z) (unique: Z) (maxu: Z) (retval: Z) (PreH1 : (strcmp_result (Znth (i) (rows) ((@nil Z))) (Znth (best) (rows) ((@nil Z))) retval )) (PreH2 : (0 <= ((string_length ((Znth (i) (rows) ((@nil Z))))) + 1 ))) (PreH3 : (0 <= ((string_length ((Znth (best) (rows) ((@nil Z))))) + 1 ))) (PreH4 : (0 <= best)) (PreH5 : (best < i)) (PreH6 : (i < words_size_pre)) (PreH7 : (j = len)) (PreH8 : (k = 256)) (PreH9 : (cur = (Znth (i) (ptrs) (0)))) (PreH10 : (max = (Znth (best) (ptrs) (0)))) (PreH11 : (better = 0)) (PreH12 : (cmp = 0)) (PreH13 : (unique = (unique_count_z_158 ((Znth (i) (rows) ((@nil Z))))))) (PreH14 : (unique = maxu)) (PreH15 : (0 < words_size_pre)) (PreH16 : (words_size_pre < INT_MAX)) (PreH17 : ((Zlength (ptrs)) = words_size_pre)) (PreH18 : (problem_158_pre_z rows )) (PreH19 : (rows_well_formed_158 rows words_size_pre )) (PreH20 : (best_state_158 rows i best maxu )) ,
  (store_string cur (Znth (i) (rows) ((@nil Z))) )
  **  (store_string max (Znth (best) (rows) ((@nil Z))) )
  **  (PtrArray.full words_pre words_size_pre ptrs )
  **  (row_stores_missing_two_158 ptrs rows best i )
  **  (IntArray.full ( &( "seen" ) ) 256 seen_l_2 )
|--
  EX (seen_l: (@list Z)) ,
  “ (0 <= best) ” 
  &&  “ (best < i) ” 
  &&  “ (i < words_size_pre) ” 
  &&  “ (j = len) ” 
  &&  “ (k = 256) ” 
  &&  “ (cur = (Znth (i) (ptrs) (0))) ” 
  &&  “ (max = (Znth (best) (ptrs) (0))) ” 
  &&  “ (better = 0) ” 
  &&  “ (unique = (unique_count_z_158 ((Znth (i) (rows) ((@nil Z)))))) ” 
  &&  “ (unique = maxu) ” 
  &&  “ (strcmp_result (Znth (i) (rows) ((@nil Z))) (Znth (best) (rows) ((@nil Z))) retval ) ” 
  &&  “ (0 < words_size_pre) ” 
  &&  “ (words_size_pre < INT_MAX) ” 
  &&  “ ((Zlength (ptrs)) = words_size_pre) ” 
  &&  “ (problem_158_pre_z rows ) ” 
  &&  “ (rows_well_formed_158 rows words_size_pre ) ” 
  &&  “ (best_state_158 rows i best maxu ) ”
  &&  (PtrArray.full words_pre words_size_pre ptrs )
  **  (row_stores_158 ptrs rows )
  **  (IntArray.full ( &( "seen" ) ) 256 seen_l )
) \/
(
forall (words_size_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (best: Z) (i: Z) (j: Z) (len: Z) (k: Z) (cur: Z) (max: Z) (better: Z) (cmp: Z) (unique: Z) (maxu: Z) (retval: Z) (PreH1 : (strcmp_result (Znth (i) (rows) ((@nil Z))) (Znth (best) (rows) ((@nil Z))) retval )) (PreH2 : (0 <= ((string_length ((Znth (i) (rows) ((@nil Z))))) + 1 ))) (PreH3 : (0 <= ((string_length ((Znth (best) (rows) ((@nil Z))))) + 1 ))) (PreH4 : (0 <= best)) (PreH5 : (best < i)) (PreH6 : (i < words_size_pre)) (PreH7 : (j = len)) (PreH8 : (k = 256)) (PreH9 : (cur = (Znth (i) (ptrs) (0)))) (PreH10 : (max = (Znth (best) (ptrs) (0)))) (PreH11 : (better = 0)) (PreH12 : (cmp = 0)) (PreH13 : (unique = (unique_count_z_158 ((Znth (i) (rows) ((@nil Z))))))) (PreH14 : (unique = maxu)) (PreH15 : (0 < words_size_pre)) (PreH16 : (words_size_pre < INT_MAX)) (PreH17 : ((Zlength (ptrs)) = words_size_pre)) (PreH18 : (problem_158_pre_z rows )) (PreH19 : (rows_well_formed_158 rows words_size_pre )) (PreH20 : (best_state_158 rows i best maxu )) ,
  (CharArray.full max ((string_length ((Znth (best) (rows) ((@nil Z))))) + 1 ) (c_string ((Znth (best) (rows) ((@nil Z))))) )
  **  (CharArray.full cur ((string_length ((Znth (i) (rows) ((@nil Z))))) + 1 ) (c_string ((Znth (i) (rows) ((@nil Z))))) )
  **  (row_stores_missing_two_158 ptrs rows best i )
|--
  (row_stores_158 ptrs rows )
).

Definition find_max_entail_wit_10_split_goal_spatial := 
forall (words_size_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (best: Z) (i: Z) (j: Z) (len: Z) (k: Z) (cur: Z) (max: Z) (better: Z) (cmp: Z) (unique: Z) (maxu: Z) (retval: Z) (PreH1 : (strcmp_result (Znth (i) (rows) ((@nil Z))) (Znth (best) (rows) ((@nil Z))) retval )) (PreH2 : (0 <= ((string_length ((Znth (i) (rows) ((@nil Z))))) + 1 ))) (PreH3 : (0 <= ((string_length ((Znth (best) (rows) ((@nil Z))))) + 1 ))) (PreH4 : (0 <= best)) (PreH5 : (best < i)) (PreH6 : (i < words_size_pre)) (PreH7 : (j = len)) (PreH8 : (k = 256)) (PreH9 : (cur = (Znth (i) (ptrs) (0)))) (PreH10 : (max = (Znth (best) (ptrs) (0)))) (PreH11 : (better = 0)) (PreH12 : (cmp = 0)) (PreH13 : (unique = (unique_count_z_158 ((Znth (i) (rows) ((@nil Z))))))) (PreH14 : (unique = maxu)) (PreH15 : (0 < words_size_pre)) (PreH16 : (words_size_pre < INT_MAX)) (PreH17 : ((Zlength (ptrs)) = words_size_pre)) (PreH18 : (problem_158_pre_z rows )) (PreH19 : (rows_well_formed_158 rows words_size_pre )) (PreH20 : (best_state_158 rows i best maxu )) ,
  (CharArray.full max ((string_length ((Znth (best) (rows) ((@nil Z))))) + 1 ) (c_string ((Znth (best) (rows) ((@nil Z))))) )
  **  (CharArray.full cur ((string_length ((Znth (i) (rows) ((@nil Z))))) + 1 ) (c_string ((Znth (i) (rows) ((@nil Z))))) )
  **  (row_stores_missing_two_158 ptrs rows best i )
|--
  (row_stores_158 ptrs rows )
.

Definition find_max_entail_wit_11_1 := 
(
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (seen_l_2: (@list Z)) (i: Z) (j: Z) (len: Z) (k: Z) (cur: Z) (max: Z) (best: Z) (unique: Z) (maxu: Z) (PreH1 : (i = best)) (PreH2 : (unique = maxu)) (PreH3 : (unique <= maxu)) (PreH4 : (0 <= i)) (PreH5 : (i < words_size_pre)) (PreH6 : (j = len)) (PreH7 : (k = 256)) (PreH8 : (cur = (Znth (i) (ptrs) (0)))) (PreH9 : (max = (Znth (best) (ptrs) (0)))) (PreH10 : (unique = (unique_count_z_158 ((Znth (i) (rows) ((@nil Z))))))) (PreH11 : (0 < words_size_pre)) (PreH12 : (words_size_pre < INT_MAX)) (PreH13 : ((Zlength (ptrs)) = words_size_pre)) (PreH14 : (problem_158_pre_z rows )) (PreH15 : (rows_well_formed_158 rows words_size_pre )) (PreH16 : (best_state_158 rows i best maxu )) ,
  (PtrArray.full words_pre words_size_pre ptrs )
  **  (row_stores_158 ptrs rows )
  **  (IntArray.full ( &( "seen" ) ) 256 seen_l_2 )
|--
  EX (seen_l: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i < words_size_pre) ” 
  &&  “ (0 < words_size_pre) ” 
  &&  “ (words_size_pre < INT_MAX) ” 
  &&  “ ((Zlength (ptrs)) = words_size_pre) ” 
  &&  “ (rows_well_formed_158 rows words_size_pre ) ” 
  &&  “ (problem_158_pre_z rows ) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best < words_size_pre) ” 
  &&  “ (max = (Znth (best) (ptrs) (0))) ” 
  &&  “ (best_state_158 rows (i + 1 ) best maxu ) ”
  &&  (PtrArray.full words_pre words_size_pre ptrs )
  **  (row_stores_158 ptrs rows )
  **  (IntArray.full ( &( "seen" ) ) 256 seen_l )
) \/
(
forall (words_size_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (i: Z) (j: Z) (len: Z) (k: Z) (cur: Z) (max: Z) (best: Z) (unique: Z) (maxu: Z) (PreH1 : (i = best)) (PreH2 : (unique = maxu)) (PreH3 : (unique <= maxu)) (PreH4 : (0 <= i)) (PreH5 : (i < words_size_pre)) (PreH6 : (j = len)) (PreH7 : (k = 256)) (PreH8 : (cur = (Znth (i) (ptrs) (0)))) (PreH9 : (max = (Znth (best) (ptrs) (0)))) (PreH10 : (unique = (unique_count_z_158 ((Znth (i) (rows) ((@nil Z))))))) (PreH11 : (0 < words_size_pre)) (PreH12 : (words_size_pre < INT_MAX)) (PreH13 : ((Zlength (ptrs)) = words_size_pre)) (PreH14 : (problem_158_pre_z rows )) (PreH15 : (rows_well_formed_158 rows words_size_pre )) (PreH16 : (best_state_158 rows i best maxu )) ,
  (row_stores_158 ptrs rows )
|--
  “ (best_state_158 rows (i + 1 ) best maxu ) ”
  &&  (row_stores_158 ptrs rows )
).

Definition find_max_entail_wit_11_1_split_goal_1 := 
forall (words_size_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (i: Z) (j: Z) (len: Z) (k: Z) (cur: Z) (max: Z) (best: Z) (unique: Z) (maxu: Z) (PreH1 : (i = best)) (PreH2 : (unique = maxu)) (PreH3 : (unique <= maxu)) (PreH4 : (0 <= i)) (PreH5 : (i < words_size_pre)) (PreH6 : (j = len)) (PreH7 : (k = 256)) (PreH8 : (cur = (Znth (i) (ptrs) (0)))) (PreH9 : (max = (Znth (best) (ptrs) (0)))) (PreH10 : (unique = (unique_count_z_158 ((Znth (i) (rows) ((@nil Z))))))) (PreH11 : (0 < words_size_pre)) (PreH12 : (words_size_pre < INT_MAX)) (PreH13 : ((Zlength (ptrs)) = words_size_pre)) (PreH14 : (problem_158_pre_z rows )) (PreH15 : (rows_well_formed_158 rows words_size_pre )) (PreH16 : (best_state_158 rows i best maxu )) ,
  (row_stores_158 ptrs rows )
|--
  “ (best_state_158 rows (i + 1 ) best maxu ) ”
.

Definition find_max_entail_wit_11_1_split_goal_spatial := 
forall (words_size_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (i: Z) (j: Z) (len: Z) (k: Z) (cur: Z) (max: Z) (best: Z) (unique: Z) (maxu: Z) (PreH1 : (i = best)) (PreH2 : (unique = maxu)) (PreH3 : (unique <= maxu)) (PreH4 : (0 <= i)) (PreH5 : (i < words_size_pre)) (PreH6 : (j = len)) (PreH7 : (k = 256)) (PreH8 : (cur = (Znth (i) (ptrs) (0)))) (PreH9 : (max = (Znth (best) (ptrs) (0)))) (PreH10 : (unique = (unique_count_z_158 ((Znth (i) (rows) ((@nil Z))))))) (PreH11 : (0 < words_size_pre)) (PreH12 : (words_size_pre < INT_MAX)) (PreH13 : ((Zlength (ptrs)) = words_size_pre)) (PreH14 : (problem_158_pre_z rows )) (PreH15 : (rows_well_formed_158 rows words_size_pre )) (PreH16 : (best_state_158 rows i best maxu )) ,
  (row_stores_158 ptrs rows )
|--
  (row_stores_158 ptrs rows )
.

Definition find_max_entail_wit_11_2 := 
(
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (seen_l_2: (@list Z)) (i: Z) (j: Z) (len: Z) (k: Z) (cur: Z) (max: Z) (best: Z) (unique: Z) (maxu: Z) (PreH1 : (unique <> maxu)) (PreH2 : (unique <= maxu)) (PreH3 : (0 <= i)) (PreH4 : (i < words_size_pre)) (PreH5 : (j = len)) (PreH6 : (k = 256)) (PreH7 : (cur = (Znth (i) (ptrs) (0)))) (PreH8 : (max = (Znth (best) (ptrs) (0)))) (PreH9 : (unique = (unique_count_z_158 ((Znth (i) (rows) ((@nil Z))))))) (PreH10 : (0 < words_size_pre)) (PreH11 : (words_size_pre < INT_MAX)) (PreH12 : ((Zlength (ptrs)) = words_size_pre)) (PreH13 : (problem_158_pre_z rows )) (PreH14 : (rows_well_formed_158 rows words_size_pre )) (PreH15 : (best_state_158 rows i best maxu )) ,
  (PtrArray.full words_pre words_size_pre ptrs )
  **  (row_stores_158 ptrs rows )
  **  (IntArray.full ( &( "seen" ) ) 256 seen_l_2 )
|--
  EX (seen_l: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i < words_size_pre) ” 
  &&  “ (0 < words_size_pre) ” 
  &&  “ (words_size_pre < INT_MAX) ” 
  &&  “ ((Zlength (ptrs)) = words_size_pre) ” 
  &&  “ (rows_well_formed_158 rows words_size_pre ) ” 
  &&  “ (problem_158_pre_z rows ) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best < words_size_pre) ” 
  &&  “ (max = (Znth (best) (ptrs) (0))) ” 
  &&  “ (best_state_158 rows (i + 1 ) best maxu ) ”
  &&  (PtrArray.full words_pre words_size_pre ptrs )
  **  (row_stores_158 ptrs rows )
  **  (IntArray.full ( &( "seen" ) ) 256 seen_l )
) \/
(
forall (words_size_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (i: Z) (j: Z) (len: Z) (k: Z) (cur: Z) (max: Z) (best: Z) (unique: Z) (maxu: Z) (PreH1 : (unique <> maxu)) (PreH2 : (unique <= maxu)) (PreH3 : (0 <= i)) (PreH4 : (i < words_size_pre)) (PreH5 : (j = len)) (PreH6 : (k = 256)) (PreH7 : (cur = (Znth (i) (ptrs) (0)))) (PreH8 : (max = (Znth (best) (ptrs) (0)))) (PreH9 : (unique = (unique_count_z_158 ((Znth (i) (rows) ((@nil Z))))))) (PreH10 : (0 < words_size_pre)) (PreH11 : (words_size_pre < INT_MAX)) (PreH12 : ((Zlength (ptrs)) = words_size_pre)) (PreH13 : (problem_158_pre_z rows )) (PreH14 : (rows_well_formed_158 rows words_size_pre )) (PreH15 : (best_state_158 rows i best maxu )) ,
  (row_stores_158 ptrs rows )
|--
  “ (best_state_158 rows (i + 1 ) best maxu ) ” 
  &&  “ (best < words_size_pre) ” 
  &&  “ (0 <= best) ”
  &&  (row_stores_158 ptrs rows )
).

Definition find_max_entail_wit_11_2_split_goal_1 := 
forall (words_size_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (i: Z) (j: Z) (len: Z) (k: Z) (cur: Z) (max: Z) (best: Z) (unique: Z) (maxu: Z) (PreH1 : (unique <> maxu)) (PreH2 : (unique <= maxu)) (PreH3 : (0 <= i)) (PreH4 : (i < words_size_pre)) (PreH5 : (j = len)) (PreH6 : (k = 256)) (PreH7 : (cur = (Znth (i) (ptrs) (0)))) (PreH8 : (max = (Znth (best) (ptrs) (0)))) (PreH9 : (unique = (unique_count_z_158 ((Znth (i) (rows) ((@nil Z))))))) (PreH10 : (0 < words_size_pre)) (PreH11 : (words_size_pre < INT_MAX)) (PreH12 : ((Zlength (ptrs)) = words_size_pre)) (PreH13 : (problem_158_pre_z rows )) (PreH14 : (rows_well_formed_158 rows words_size_pre )) (PreH15 : (best_state_158 rows i best maxu )) ,
  (row_stores_158 ptrs rows )
|--
  “ (best_state_158 rows (i + 1 ) best maxu ) ”
.

Definition find_max_entail_wit_11_2_split_goal_2 := 
forall (words_size_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (i: Z) (j: Z) (len: Z) (k: Z) (cur: Z) (max: Z) (best: Z) (unique: Z) (maxu: Z) (PreH1 : (unique <> maxu)) (PreH2 : (unique <= maxu)) (PreH3 : (0 <= i)) (PreH4 : (i < words_size_pre)) (PreH5 : (j = len)) (PreH6 : (k = 256)) (PreH7 : (cur = (Znth (i) (ptrs) (0)))) (PreH8 : (max = (Znth (best) (ptrs) (0)))) (PreH9 : (unique = (unique_count_z_158 ((Znth (i) (rows) ((@nil Z))))))) (PreH10 : (0 < words_size_pre)) (PreH11 : (words_size_pre < INT_MAX)) (PreH12 : ((Zlength (ptrs)) = words_size_pre)) (PreH13 : (problem_158_pre_z rows )) (PreH14 : (rows_well_formed_158 rows words_size_pre )) (PreH15 : (best_state_158 rows i best maxu )) ,
  (row_stores_158 ptrs rows )
|--
  “ (best < words_size_pre) ”
.

Definition find_max_entail_wit_11_2_split_goal_3 := 
forall (words_size_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (i: Z) (j: Z) (len: Z) (k: Z) (cur: Z) (max: Z) (best: Z) (unique: Z) (maxu: Z) (PreH1 : (unique <> maxu)) (PreH2 : (unique <= maxu)) (PreH3 : (0 <= i)) (PreH4 : (i < words_size_pre)) (PreH5 : (j = len)) (PreH6 : (k = 256)) (PreH7 : (cur = (Znth (i) (ptrs) (0)))) (PreH8 : (max = (Znth (best) (ptrs) (0)))) (PreH9 : (unique = (unique_count_z_158 ((Znth (i) (rows) ((@nil Z))))))) (PreH10 : (0 < words_size_pre)) (PreH11 : (words_size_pre < INT_MAX)) (PreH12 : ((Zlength (ptrs)) = words_size_pre)) (PreH13 : (problem_158_pre_z rows )) (PreH14 : (rows_well_formed_158 rows words_size_pre )) (PreH15 : (best_state_158 rows i best maxu )) ,
  (row_stores_158 ptrs rows )
|--
  “ (0 <= best) ”
.

Definition find_max_entail_wit_11_2_split_goal_spatial := 
forall (words_size_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (i: Z) (j: Z) (len: Z) (k: Z) (cur: Z) (max: Z) (best: Z) (unique: Z) (maxu: Z) (PreH1 : (unique <> maxu)) (PreH2 : (unique <= maxu)) (PreH3 : (0 <= i)) (PreH4 : (i < words_size_pre)) (PreH5 : (j = len)) (PreH6 : (k = 256)) (PreH7 : (cur = (Znth (i) (ptrs) (0)))) (PreH8 : (max = (Znth (best) (ptrs) (0)))) (PreH9 : (unique = (unique_count_z_158 ((Znth (i) (rows) ((@nil Z))))))) (PreH10 : (0 < words_size_pre)) (PreH11 : (words_size_pre < INT_MAX)) (PreH12 : ((Zlength (ptrs)) = words_size_pre)) (PreH13 : (problem_158_pre_z rows )) (PreH14 : (rows_well_formed_158 rows words_size_pre )) (PreH15 : (best_state_158 rows i best maxu )) ,
  (row_stores_158 ptrs rows )
|--
  (row_stores_158 ptrs rows )
.

Definition find_max_entail_wit_11_3 := 
(
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (seen_l_2: (@list Z)) (best: Z) (i: Z) (j: Z) (len: Z) (k: Z) (cur: Z) (max: Z) (better: Z) (cmp: Z) (unique: Z) (maxu: Z) (PreH1 : (better = 0)) (PreH2 : (cmp >= 0)) (PreH3 : (0 <= best)) (PreH4 : (best < i)) (PreH5 : (i < words_size_pre)) (PreH6 : (j = len)) (PreH7 : (k = 256)) (PreH8 : (cur = (Znth (i) (ptrs) (0)))) (PreH9 : (max = (Znth (best) (ptrs) (0)))) (PreH10 : (better = 0)) (PreH11 : (unique = (unique_count_z_158 ((Znth (i) (rows) ((@nil Z))))))) (PreH12 : (unique = maxu)) (PreH13 : (strcmp_result (Znth (i) (rows) ((@nil Z))) (Znth (best) (rows) ((@nil Z))) cmp )) (PreH14 : (0 < words_size_pre)) (PreH15 : (words_size_pre < INT_MAX)) (PreH16 : ((Zlength (ptrs)) = words_size_pre)) (PreH17 : (problem_158_pre_z rows )) (PreH18 : (rows_well_formed_158 rows words_size_pre )) (PreH19 : (best_state_158 rows i best maxu )) ,
  (PtrArray.full words_pre words_size_pre ptrs )
  **  (row_stores_158 ptrs rows )
  **  (IntArray.full ( &( "seen" ) ) 256 seen_l_2 )
|--
  EX (seen_l: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i < words_size_pre) ” 
  &&  “ (0 < words_size_pre) ” 
  &&  “ (words_size_pre < INT_MAX) ” 
  &&  “ ((Zlength (ptrs)) = words_size_pre) ” 
  &&  “ (rows_well_formed_158 rows words_size_pre ) ” 
  &&  “ (problem_158_pre_z rows ) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best < words_size_pre) ” 
  &&  “ (max = (Znth (best) (ptrs) (0))) ” 
  &&  “ (best_state_158 rows (i + 1 ) best maxu ) ”
  &&  (PtrArray.full words_pre words_size_pre ptrs )
  **  (row_stores_158 ptrs rows )
  **  (IntArray.full ( &( "seen" ) ) 256 seen_l )
) \/
(
forall (words_size_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (best: Z) (i: Z) (j: Z) (len: Z) (k: Z) (cur: Z) (max: Z) (better: Z) (cmp: Z) (unique: Z) (maxu: Z) (PreH1 : (better = 0)) (PreH2 : (cmp >= 0)) (PreH3 : (0 <= best)) (PreH4 : (best < i)) (PreH5 : (i < words_size_pre)) (PreH6 : (j = len)) (PreH7 : (k = 256)) (PreH8 : (cur = (Znth (i) (ptrs) (0)))) (PreH9 : (max = (Znth (best) (ptrs) (0)))) (PreH10 : (better = 0)) (PreH11 : (unique = (unique_count_z_158 ((Znth (i) (rows) ((@nil Z))))))) (PreH12 : (unique = maxu)) (PreH13 : (strcmp_result (Znth (i) (rows) ((@nil Z))) (Znth (best) (rows) ((@nil Z))) cmp )) (PreH14 : (0 < words_size_pre)) (PreH15 : (words_size_pre < INT_MAX)) (PreH16 : ((Zlength (ptrs)) = words_size_pre)) (PreH17 : (problem_158_pre_z rows )) (PreH18 : (rows_well_formed_158 rows words_size_pre )) (PreH19 : (best_state_158 rows i best maxu )) ,
  (row_stores_158 ptrs rows )
|--
  “ (best_state_158 rows (i + 1 ) best maxu ) ”
  &&  (row_stores_158 ptrs rows )
).

Definition find_max_entail_wit_11_3_split_goal_1 := 
forall (words_size_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (best: Z) (i: Z) (j: Z) (len: Z) (k: Z) (cur: Z) (max: Z) (better: Z) (cmp: Z) (unique: Z) (maxu: Z) (PreH1 : (better = 0)) (PreH2 : (cmp >= 0)) (PreH3 : (0 <= best)) (PreH4 : (best < i)) (PreH5 : (i < words_size_pre)) (PreH6 : (j = len)) (PreH7 : (k = 256)) (PreH8 : (cur = (Znth (i) (ptrs) (0)))) (PreH9 : (max = (Znth (best) (ptrs) (0)))) (PreH10 : (better = 0)) (PreH11 : (unique = (unique_count_z_158 ((Znth (i) (rows) ((@nil Z))))))) (PreH12 : (unique = maxu)) (PreH13 : (strcmp_result (Znth (i) (rows) ((@nil Z))) (Znth (best) (rows) ((@nil Z))) cmp )) (PreH14 : (0 < words_size_pre)) (PreH15 : (words_size_pre < INT_MAX)) (PreH16 : ((Zlength (ptrs)) = words_size_pre)) (PreH17 : (problem_158_pre_z rows )) (PreH18 : (rows_well_formed_158 rows words_size_pre )) (PreH19 : (best_state_158 rows i best maxu )) ,
  (row_stores_158 ptrs rows )
|--
  “ (best_state_158 rows (i + 1 ) best maxu ) ”
.

Definition find_max_entail_wit_11_3_split_goal_spatial := 
forall (words_size_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (best: Z) (i: Z) (j: Z) (len: Z) (k: Z) (cur: Z) (max: Z) (better: Z) (cmp: Z) (unique: Z) (maxu: Z) (PreH1 : (better = 0)) (PreH2 : (cmp >= 0)) (PreH3 : (0 <= best)) (PreH4 : (best < i)) (PreH5 : (i < words_size_pre)) (PreH6 : (j = len)) (PreH7 : (k = 256)) (PreH8 : (cur = (Znth (i) (ptrs) (0)))) (PreH9 : (max = (Znth (best) (ptrs) (0)))) (PreH10 : (better = 0)) (PreH11 : (unique = (unique_count_z_158 ((Znth (i) (rows) ((@nil Z))))))) (PreH12 : (unique = maxu)) (PreH13 : (strcmp_result (Znth (i) (rows) ((@nil Z))) (Znth (best) (rows) ((@nil Z))) cmp )) (PreH14 : (0 < words_size_pre)) (PreH15 : (words_size_pre < INT_MAX)) (PreH16 : ((Zlength (ptrs)) = words_size_pre)) (PreH17 : (problem_158_pre_z rows )) (PreH18 : (rows_well_formed_158 rows words_size_pre )) (PreH19 : (best_state_158 rows i best maxu )) ,
  (row_stores_158 ptrs rows )
|--
  (row_stores_158 ptrs rows )
.

Definition find_max_entail_wit_11_4 := 
(
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (seen_l_2: (@list Z)) (best: Z) (i: Z) (j: Z) (len: Z) (k: Z) (cur: Z) (max: Z) (better: Z) (cmp: Z) (unique: Z) (maxu: Z) (PreH1 : (cmp < 0)) (PreH2 : (0 <= best)) (PreH3 : (best < i)) (PreH4 : (i < words_size_pre)) (PreH5 : (j = len)) (PreH6 : (k = 256)) (PreH7 : (cur = (Znth (i) (ptrs) (0)))) (PreH8 : (max = (Znth (best) (ptrs) (0)))) (PreH9 : (better = 0)) (PreH10 : (unique = (unique_count_z_158 ((Znth (i) (rows) ((@nil Z))))))) (PreH11 : (unique = maxu)) (PreH12 : (strcmp_result (Znth (i) (rows) ((@nil Z))) (Znth (best) (rows) ((@nil Z))) cmp )) (PreH13 : (0 < words_size_pre)) (PreH14 : (words_size_pre < INT_MAX)) (PreH15 : ((Zlength (ptrs)) = words_size_pre)) (PreH16 : (problem_158_pre_z rows )) (PreH17 : (rows_well_formed_158 rows words_size_pre )) (PreH18 : (best_state_158 rows i best maxu )) ,
  (PtrArray.full words_pre words_size_pre ptrs )
  **  (row_stores_158 ptrs rows )
  **  (IntArray.full ( &( "seen" ) ) 256 seen_l_2 )
|--
  EX (seen_l: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i < words_size_pre) ” 
  &&  “ (0 < words_size_pre) ” 
  &&  “ (words_size_pre < INT_MAX) ” 
  &&  “ ((Zlength (ptrs)) = words_size_pre) ” 
  &&  “ (rows_well_formed_158 rows words_size_pre ) ” 
  &&  “ (problem_158_pre_z rows ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < words_size_pre) ” 
  &&  “ (cur = (Znth (i) (ptrs) (0))) ” 
  &&  “ (best_state_158 rows (i + 1 ) i unique ) ”
  &&  (PtrArray.full words_pre words_size_pre ptrs )
  **  (row_stores_158 ptrs rows )
  **  (IntArray.full ( &( "seen" ) ) 256 seen_l )
) \/
(
forall (words_size_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (best: Z) (i: Z) (j: Z) (len: Z) (k: Z) (cur: Z) (max: Z) (better: Z) (cmp: Z) (unique: Z) (maxu: Z) (PreH1 : (cmp < 0)) (PreH2 : (0 <= best)) (PreH3 : (best < i)) (PreH4 : (i < words_size_pre)) (PreH5 : (j = len)) (PreH6 : (k = 256)) (PreH7 : (cur = (Znth (i) (ptrs) (0)))) (PreH8 : (max = (Znth (best) (ptrs) (0)))) (PreH9 : (better = 0)) (PreH10 : (unique = (unique_count_z_158 ((Znth (i) (rows) ((@nil Z))))))) (PreH11 : (unique = maxu)) (PreH12 : (strcmp_result (Znth (i) (rows) ((@nil Z))) (Znth (best) (rows) ((@nil Z))) cmp )) (PreH13 : (0 < words_size_pre)) (PreH14 : (words_size_pre < INT_MAX)) (PreH15 : ((Zlength (ptrs)) = words_size_pre)) (PreH16 : (problem_158_pre_z rows )) (PreH17 : (rows_well_formed_158 rows words_size_pre )) (PreH18 : (best_state_158 rows i best maxu )) ,
  (row_stores_158 ptrs rows )
|--
  “ (best_state_158 rows (i + 1 ) i unique ) ”
  &&  (row_stores_158 ptrs rows )
).

Definition find_max_entail_wit_11_4_split_goal_1 := 
forall (words_size_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (best: Z) (i: Z) (j: Z) (len: Z) (k: Z) (cur: Z) (max: Z) (better: Z) (cmp: Z) (unique: Z) (maxu: Z) (PreH1 : (cmp < 0)) (PreH2 : (0 <= best)) (PreH3 : (best < i)) (PreH4 : (i < words_size_pre)) (PreH5 : (j = len)) (PreH6 : (k = 256)) (PreH7 : (cur = (Znth (i) (ptrs) (0)))) (PreH8 : (max = (Znth (best) (ptrs) (0)))) (PreH9 : (better = 0)) (PreH10 : (unique = (unique_count_z_158 ((Znth (i) (rows) ((@nil Z))))))) (PreH11 : (unique = maxu)) (PreH12 : (strcmp_result (Znth (i) (rows) ((@nil Z))) (Znth (best) (rows) ((@nil Z))) cmp )) (PreH13 : (0 < words_size_pre)) (PreH14 : (words_size_pre < INT_MAX)) (PreH15 : ((Zlength (ptrs)) = words_size_pre)) (PreH16 : (problem_158_pre_z rows )) (PreH17 : (rows_well_formed_158 rows words_size_pre )) (PreH18 : (best_state_158 rows i best maxu )) ,
  (row_stores_158 ptrs rows )
|--
  “ (best_state_158 rows (i + 1 ) i unique ) ”
.

Definition find_max_entail_wit_11_4_split_goal_spatial := 
forall (words_size_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (best: Z) (i: Z) (j: Z) (len: Z) (k: Z) (cur: Z) (max: Z) (better: Z) (cmp: Z) (unique: Z) (maxu: Z) (PreH1 : (cmp < 0)) (PreH2 : (0 <= best)) (PreH3 : (best < i)) (PreH4 : (i < words_size_pre)) (PreH5 : (j = len)) (PreH6 : (k = 256)) (PreH7 : (cur = (Znth (i) (ptrs) (0)))) (PreH8 : (max = (Znth (best) (ptrs) (0)))) (PreH9 : (better = 0)) (PreH10 : (unique = (unique_count_z_158 ((Znth (i) (rows) ((@nil Z))))))) (PreH11 : (unique = maxu)) (PreH12 : (strcmp_result (Znth (i) (rows) ((@nil Z))) (Znth (best) (rows) ((@nil Z))) cmp )) (PreH13 : (0 < words_size_pre)) (PreH14 : (words_size_pre < INT_MAX)) (PreH15 : ((Zlength (ptrs)) = words_size_pre)) (PreH16 : (problem_158_pre_z rows )) (PreH17 : (rows_well_formed_158 rows words_size_pre )) (PreH18 : (best_state_158 rows i best maxu )) ,
  (row_stores_158 ptrs rows )
|--
  (row_stores_158 ptrs rows )
.

Definition find_max_entail_wit_11_5 := 
(
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (seen_l_2: (@list Z)) (i: Z) (j: Z) (len: Z) (k: Z) (cur: Z) (max: Z) (best: Z) (unique: Z) (maxu: Z) (PreH1 : (unique > maxu)) (PreH2 : (0 <= i)) (PreH3 : (i < words_size_pre)) (PreH4 : (j = len)) (PreH5 : (k = 256)) (PreH6 : (cur = (Znth (i) (ptrs) (0)))) (PreH7 : (max = (Znth (best) (ptrs) (0)))) (PreH8 : (unique = (unique_count_z_158 ((Znth (i) (rows) ((@nil Z))))))) (PreH9 : (0 < words_size_pre)) (PreH10 : (words_size_pre < INT_MAX)) (PreH11 : ((Zlength (ptrs)) = words_size_pre)) (PreH12 : (problem_158_pre_z rows )) (PreH13 : (rows_well_formed_158 rows words_size_pre )) (PreH14 : (best_state_158 rows i best maxu )) ,
  (PtrArray.full words_pre words_size_pre ptrs )
  **  (row_stores_158 ptrs rows )
  **  (IntArray.full ( &( "seen" ) ) 256 seen_l_2 )
|--
  EX (seen_l: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i < words_size_pre) ” 
  &&  “ (0 < words_size_pre) ” 
  &&  “ (words_size_pre < INT_MAX) ” 
  &&  “ ((Zlength (ptrs)) = words_size_pre) ” 
  &&  “ (rows_well_formed_158 rows words_size_pre ) ” 
  &&  “ (problem_158_pre_z rows ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < words_size_pre) ” 
  &&  “ (cur = (Znth (i) (ptrs) (0))) ” 
  &&  “ (best_state_158 rows (i + 1 ) i unique ) ”
  &&  (PtrArray.full words_pre words_size_pre ptrs )
  **  (row_stores_158 ptrs rows )
  **  (IntArray.full ( &( "seen" ) ) 256 seen_l )
) \/
(
forall (words_size_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (i: Z) (j: Z) (len: Z) (k: Z) (cur: Z) (max: Z) (best: Z) (unique: Z) (maxu: Z) (PreH1 : (unique > maxu)) (PreH2 : (0 <= i)) (PreH3 : (i < words_size_pre)) (PreH4 : (j = len)) (PreH5 : (k = 256)) (PreH6 : (cur = (Znth (i) (ptrs) (0)))) (PreH7 : (max = (Znth (best) (ptrs) (0)))) (PreH8 : (unique = (unique_count_z_158 ((Znth (i) (rows) ((@nil Z))))))) (PreH9 : (0 < words_size_pre)) (PreH10 : (words_size_pre < INT_MAX)) (PreH11 : ((Zlength (ptrs)) = words_size_pre)) (PreH12 : (problem_158_pre_z rows )) (PreH13 : (rows_well_formed_158 rows words_size_pre )) (PreH14 : (best_state_158 rows i best maxu )) ,
  (row_stores_158 ptrs rows )
|--
  “ (best_state_158 rows (i + 1 ) i unique ) ”
  &&  (row_stores_158 ptrs rows )
).

Definition find_max_entail_wit_11_5_split_goal_1 := 
forall (words_size_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (i: Z) (j: Z) (len: Z) (k: Z) (cur: Z) (max: Z) (best: Z) (unique: Z) (maxu: Z) (PreH1 : (unique > maxu)) (PreH2 : (0 <= i)) (PreH3 : (i < words_size_pre)) (PreH4 : (j = len)) (PreH5 : (k = 256)) (PreH6 : (cur = (Znth (i) (ptrs) (0)))) (PreH7 : (max = (Znth (best) (ptrs) (0)))) (PreH8 : (unique = (unique_count_z_158 ((Znth (i) (rows) ((@nil Z))))))) (PreH9 : (0 < words_size_pre)) (PreH10 : (words_size_pre < INT_MAX)) (PreH11 : ((Zlength (ptrs)) = words_size_pre)) (PreH12 : (problem_158_pre_z rows )) (PreH13 : (rows_well_formed_158 rows words_size_pre )) (PreH14 : (best_state_158 rows i best maxu )) ,
  (row_stores_158 ptrs rows )
|--
  “ (best_state_158 rows (i + 1 ) i unique ) ”
.

Definition find_max_entail_wit_11_5_split_goal_spatial := 
forall (words_size_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (i: Z) (j: Z) (len: Z) (k: Z) (cur: Z) (max: Z) (best: Z) (unique: Z) (maxu: Z) (PreH1 : (unique > maxu)) (PreH2 : (0 <= i)) (PreH3 : (i < words_size_pre)) (PreH4 : (j = len)) (PreH5 : (k = 256)) (PreH6 : (cur = (Znth (i) (ptrs) (0)))) (PreH7 : (max = (Znth (best) (ptrs) (0)))) (PreH8 : (unique = (unique_count_z_158 ((Znth (i) (rows) ((@nil Z))))))) (PreH9 : (0 < words_size_pre)) (PreH10 : (words_size_pre < INT_MAX)) (PreH11 : ((Zlength (ptrs)) = words_size_pre)) (PreH12 : (problem_158_pre_z rows )) (PreH13 : (rows_well_formed_158 rows words_size_pre )) (PreH14 : (best_state_158 rows i best maxu )) ,
  (row_stores_158 ptrs rows )
|--
  (row_stores_158 ptrs rows )
.

Definition find_max_entail_wit_12 := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (i: Z) (best: Z) (max: Z) (maxu: Z) (PreH1 : (0 <= i)) (PreH2 : (i < words_size_pre)) (PreH3 : (0 < words_size_pre)) (PreH4 : (words_size_pre < INT_MAX)) (PreH5 : ((Zlength (ptrs)) = words_size_pre)) (PreH6 : (rows_well_formed_158 rows words_size_pre )) (PreH7 : (problem_158_pre_z rows )) (PreH8 : (0 <= best)) (PreH9 : (best < words_size_pre)) (PreH10 : (max = (Znth (best) (ptrs) (0)))) (PreH11 : (best_state_158 rows (i + 1 ) best maxu )) ,
  (PtrArray.full words_pre words_size_pre ptrs )
  **  (row_stores_158 ptrs rows )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= words_size_pre) ” 
  &&  “ (0 < words_size_pre) ” 
  &&  “ (words_size_pre < INT_MAX) ” 
  &&  “ ((Zlength (ptrs)) = words_size_pre) ” 
  &&  “ (rows_well_formed_158 rows words_size_pre ) ” 
  &&  “ (problem_158_pre_z rows ) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best < words_size_pre) ” 
  &&  “ (max = (Znth (best) (ptrs) (0))) ” 
  &&  “ (best_state_158 rows (i + 1 ) best maxu ) ”
  &&  (PtrArray.full words_pre words_size_pre ptrs )
  **  (row_stores_158 ptrs rows )
.

Definition find_max_return_wit_1 := 
(
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (maxu: Z) (max: Z) (best_2: Z) (i: Z) (PreH1 : (i >= words_size_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= words_size_pre)) (PreH4 : (0 < words_size_pre)) (PreH5 : (words_size_pre < INT_MAX)) (PreH6 : ((Zlength (ptrs)) = words_size_pre)) (PreH7 : (rows_well_formed_158 rows words_size_pre )) (PreH8 : (problem_158_pre_z rows )) (PreH9 : (0 <= best_2)) (PreH10 : (best_2 < words_size_pre)) (PreH11 : (max = (Znth (best_2) (ptrs) (0)))) (PreH12 : (best_state_158 rows i best_2 maxu )) ,
  (PtrArray.full words_pre words_size_pre ptrs )
  **  (row_stores_158 ptrs rows )
|--
  EX (best: Z) ,
  “ (0 <= best) ” 
  &&  “ (best < words_size_pre) ” 
  &&  “ (max = (Znth (best) (ptrs) (0))) ” 
  &&  “ (problem_158_spec_z rows (Znth (best) (rows) ((@nil Z))) ) ”
  &&  (PtrArray.full words_pre words_size_pre ptrs )
  **  (row_stores_158 ptrs rows )
) \/
(
forall (words_size_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (maxu: Z) (max: Z) (best_2: Z) (i: Z) (PreH1 : (i >= words_size_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= words_size_pre)) (PreH4 : (0 < words_size_pre)) (PreH5 : (words_size_pre < INT_MAX)) (PreH6 : ((Zlength (ptrs)) = words_size_pre)) (PreH7 : (rows_well_formed_158 rows words_size_pre )) (PreH8 : (problem_158_pre_z rows )) (PreH9 : (0 <= best_2)) (PreH10 : (best_2 < words_size_pre)) (PreH11 : (max = (Znth (best_2) (ptrs) (0)))) (PreH12 : (best_state_158 rows i best_2 maxu )) ,
  (row_stores_158 ptrs rows )
|--
  EX (best: Z) ,
  “ (0 <= best) ” 
  &&  “ (best < words_size_pre) ” 
  &&  “ (max = (Znth (best) (ptrs) (0))) ” 
  &&  “ (problem_158_spec_z rows (Znth (best) (rows) ((@nil Z))) ) ”
  &&  (row_stores_158 ptrs rows )
).

Definition find_max_partial_solve_wit_1 := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (PreH1 : (0 < words_size_pre)) (PreH2 : (words_size_pre < INT_MAX)) (PreH3 : ((Zlength (ptrs)) = words_size_pre)) (PreH4 : (rows_well_formed_158 rows words_size_pre )) (PreH5 : (problem_158_pre_z rows )) ,
  (PtrArray.full words_pre words_size_pre ptrs )
  **  (row_stores_158 ptrs rows )
|--
  “ (0 < words_size_pre) ” 
  &&  “ (words_size_pre < INT_MAX) ” 
  &&  “ ((Zlength (ptrs)) = words_size_pre) ” 
  &&  “ (rows_well_formed_158 rows words_size_pre ) ” 
  &&  “ (problem_158_pre_z rows ) ”
  &&  (((words_pre + (0 * sizeof(PTR) ) )) # Ptr  |-> (Znth 0 ptrs 0))
  **  (PtrArray.missing_i words_pre 0 0 words_size_pre ptrs )
  **  (row_stores_158 ptrs rows )
.

Definition find_max_partial_solve_wit_2 := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (maxu: Z) (max: Z) (best: Z) (i: Z) (PreH1 : (i < words_size_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= words_size_pre)) (PreH4 : (0 < words_size_pre)) (PreH5 : (words_size_pre < INT_MAX)) (PreH6 : ((Zlength (ptrs)) = words_size_pre)) (PreH7 : (rows_well_formed_158 rows words_size_pre )) (PreH8 : (problem_158_pre_z rows )) (PreH9 : (0 <= best)) (PreH10 : (best < words_size_pre)) (PreH11 : (max = (Znth (best) (ptrs) (0)))) (PreH12 : (best_state_158 rows i best maxu )) ,
  (PtrArray.full words_pre words_size_pre ptrs )
  **  (row_stores_158 ptrs rows )
|--
  “ (i < words_size_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= words_size_pre) ” 
  &&  “ (0 < words_size_pre) ” 
  &&  “ (words_size_pre < INT_MAX) ” 
  &&  “ ((Zlength (ptrs)) = words_size_pre) ” 
  &&  “ (rows_well_formed_158 rows words_size_pre ) ” 
  &&  “ (problem_158_pre_z rows ) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best < words_size_pre) ” 
  &&  “ (max = (Znth (best) (ptrs) (0))) ” 
  &&  “ (best_state_158 rows i best maxu ) ”
  &&  (((words_pre + (i * sizeof(PTR) ) )) # Ptr  |-> (Znth i ptrs 0))
  **  (PtrArray.missing_i words_pre i 0 words_size_pre ptrs )
  **  (row_stores_158 ptrs rows )
.

Definition find_max_partial_solve_wit_3 := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (maxu: Z) (best: Z) (max: Z) (cur: Z) (i: Z) (zeros: (@list Z)) (k: Z) (PreH1 : (k < 256)) (PreH2 : (0 <= k)) (PreH3 : (k <= 256)) (PreH4 : (zeros = (repeat_Z (0) (k)))) (PreH5 : (0 <= i)) (PreH6 : (i < words_size_pre)) (PreH7 : (cur = (Znth (i) (ptrs) (0)))) (PreH8 : (max = (Znth (best) (ptrs) (0)))) (PreH9 : (0 < words_size_pre)) (PreH10 : (words_size_pre < INT_MAX)) (PreH11 : (0 <= best)) (PreH12 : (best < words_size_pre)) (PreH13 : ((Zlength (ptrs)) = words_size_pre)) (PreH14 : (rows_well_formed_158 rows words_size_pre )) (PreH15 : (problem_158_pre_z rows )) (PreH16 : (best_state_158 rows i best maxu )) ,
  (PtrArray.full words_pre words_size_pre ptrs )
  **  (row_stores_158 ptrs rows )
  **  (IntArray.seg ( &( "seen" ) ) 0 k zeros )
  **  (IntArray.undef_seg ( &( "seen" ) ) k 256 )
|--
  “ (k < 256) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= 256) ” 
  &&  “ (zeros = (repeat_Z (0) (k))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < words_size_pre) ” 
  &&  “ (cur = (Znth (i) (ptrs) (0))) ” 
  &&  “ (max = (Znth (best) (ptrs) (0))) ” 
  &&  “ (0 < words_size_pre) ” 
  &&  “ (words_size_pre < INT_MAX) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best < words_size_pre) ” 
  &&  “ ((Zlength (ptrs)) = words_size_pre) ” 
  &&  “ (rows_well_formed_158 rows words_size_pre ) ” 
  &&  “ (problem_158_pre_z rows ) ” 
  &&  “ (best_state_158 rows i best maxu ) ”
  &&  (((( &( "seen" ) ) + (k * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg ( &( "seen" ) ) (k + 1 ) 256 )
  **  (PtrArray.full words_pre words_size_pre ptrs )
  **  (row_stores_158 ptrs rows )
  **  (IntArray.seg ( &( "seen" ) ) 0 k zeros )
.

Definition find_max_partial_solve_wit_4_pure := 
(
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (i: Z) (k: Z) (cur: Z) (max: Z) (best: Z) (maxu: Z) (PreH1 : (0 <= i)) (PreH2 : (i < words_size_pre)) (PreH3 : (k = 256)) (PreH4 : (cur = (Znth (i) (ptrs) (0)))) (PreH5 : (max = (Znth (best) (ptrs) (0)))) (PreH6 : (0 < words_size_pre)) (PreH7 : (words_size_pre < INT_MAX)) (PreH8 : ((Zlength (ptrs)) = words_size_pre)) (PreH9 : (problem_158_pre_z rows )) (PreH10 : (rows_well_formed_158 rows words_size_pre )) (PreH11 : (best_state_158 rows i best maxu )) ,
  ((( &( "len" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "words_size" ) )) # Int  |-> words_size_pre)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "max" ) )) # Ptr  |-> max)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "maxu" ) )) # Int  |-> maxu)
  **  (PtrArray.full words_pre words_size_pre ptrs )
  **  (row_stores_missing_i_158 ptrs rows i )
  **  (store_string cur (Znth (i) (rows) ((@nil Z))) )
  **  (IntArray.full ( &( "seen" ) ) 256 (repeat_Z (0) (256)) )
|--
  “ ((string_length ((Znth (i) (rows) ((@nil Z))))) < INT_MAX) ” 
  &&  “ (valid_string (Znth (i) (rows) ((@nil Z))) ) ”
) \/
(
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (i: Z) (k: Z) (cur: Z) (max: Z) (best: Z) (maxu: Z) (PreH1 : (maxu <= INT_MAX)) (PreH2 : (best <= INT_MAX)) (PreH3 : (words_size_pre <= INT_MAX)) (PreH4 : (k <= INT_MAX)) (PreH5 : (i <= INT_MAX)) (PreH6 : (maxu >= INT_MIN)) (PreH7 : (best >= INT_MIN)) (PreH8 : (words_size_pre >= INT_MIN)) (PreH9 : (k >= INT_MIN)) (PreH10 : (i >= INT_MIN)) (PreH11 : (0 <= ((string_length ((Znth (i) (rows) ((@nil Z))))) + 1 ))) (PreH12 : (0 <= i)) (PreH13 : (i < words_size_pre)) (PreH14 : (k = 256)) (PreH15 : (cur = (Znth (i) (ptrs) (0)))) (PreH16 : (max = (Znth (best) (ptrs) (0)))) (PreH17 : (0 < words_size_pre)) (PreH18 : (words_size_pre < INT_MAX)) (PreH19 : ((Zlength (ptrs)) = words_size_pre)) (PreH20 : (problem_158_pre_z rows )) (PreH21 : (rows_well_formed_158 rows words_size_pre )) (PreH22 : (best_state_158 rows i best maxu )) ,
  (CharArray.full cur ((string_length ((Znth (i) (rows) ((@nil Z))))) + 1 ) (c_string ((Znth (i) (rows) ((@nil Z))))) )
  **  ((( &( "len" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "words_size" ) )) # Int  |-> words_size_pre)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "max" ) )) # Ptr  |-> max)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "maxu" ) )) # Int  |-> maxu)
  **  (PtrArray.full words_pre words_size_pre ptrs )
  **  (row_stores_missing_i_158 ptrs rows i )
  **  (IntArray.full ( &( "seen" ) ) 256 (repeat_Z (0) (256)) )
|--
  “ (valid_string (Znth (i) (rows) ((@nil Z))) ) ” 
  &&  “ ((string_length ((Znth (i) (rows) ((@nil Z))))) < INT_MAX) ”
).

Definition find_max_partial_solve_wit_4_pure_split_goal_1 := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (i: Z) (k: Z) (cur: Z) (max: Z) (best: Z) (maxu: Z) (PreH1 : (maxu <= INT_MAX)) (PreH2 : (best <= INT_MAX)) (PreH3 : (words_size_pre <= INT_MAX)) (PreH4 : (k <= INT_MAX)) (PreH5 : (i <= INT_MAX)) (PreH6 : (maxu >= INT_MIN)) (PreH7 : (best >= INT_MIN)) (PreH8 : (words_size_pre >= INT_MIN)) (PreH9 : (k >= INT_MIN)) (PreH10 : (i >= INT_MIN)) (PreH11 : (0 <= ((string_length ((Znth (i) (rows) ((@nil Z))))) + 1 ))) (PreH12 : (0 <= i)) (PreH13 : (i < words_size_pre)) (PreH14 : (k = 256)) (PreH15 : (cur = (Znth (i) (ptrs) (0)))) (PreH16 : (max = (Znth (best) (ptrs) (0)))) (PreH17 : (0 < words_size_pre)) (PreH18 : (words_size_pre < INT_MAX)) (PreH19 : ((Zlength (ptrs)) = words_size_pre)) (PreH20 : (problem_158_pre_z rows )) (PreH21 : (rows_well_formed_158 rows words_size_pre )) (PreH22 : (best_state_158 rows i best maxu )) ,
  (CharArray.full cur ((string_length ((Znth (i) (rows) ((@nil Z))))) + 1 ) (c_string ((Znth (i) (rows) ((@nil Z))))) )
  **  ((( &( "len" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "words_size" ) )) # Int  |-> words_size_pre)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "max" ) )) # Ptr  |-> max)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "maxu" ) )) # Int  |-> maxu)
  **  (PtrArray.full words_pre words_size_pre ptrs )
  **  (row_stores_missing_i_158 ptrs rows i )
  **  (IntArray.full ( &( "seen" ) ) 256 (repeat_Z (0) (256)) )
|--
  “ (valid_string (Znth (i) (rows) ((@nil Z))) ) ”
.

Definition find_max_partial_solve_wit_4_pure_split_goal_2 := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (i: Z) (k: Z) (cur: Z) (max: Z) (best: Z) (maxu: Z) (PreH1 : (maxu <= INT_MAX)) (PreH2 : (best <= INT_MAX)) (PreH3 : (words_size_pre <= INT_MAX)) (PreH4 : (k <= INT_MAX)) (PreH5 : (i <= INT_MAX)) (PreH6 : (maxu >= INT_MIN)) (PreH7 : (best >= INT_MIN)) (PreH8 : (words_size_pre >= INT_MIN)) (PreH9 : (k >= INT_MIN)) (PreH10 : (i >= INT_MIN)) (PreH11 : (0 <= ((string_length ((Znth (i) (rows) ((@nil Z))))) + 1 ))) (PreH12 : (0 <= i)) (PreH13 : (i < words_size_pre)) (PreH14 : (k = 256)) (PreH15 : (cur = (Znth (i) (ptrs) (0)))) (PreH16 : (max = (Znth (best) (ptrs) (0)))) (PreH17 : (0 < words_size_pre)) (PreH18 : (words_size_pre < INT_MAX)) (PreH19 : ((Zlength (ptrs)) = words_size_pre)) (PreH20 : (problem_158_pre_z rows )) (PreH21 : (rows_well_formed_158 rows words_size_pre )) (PreH22 : (best_state_158 rows i best maxu )) ,
  (CharArray.full cur ((string_length ((Znth (i) (rows) ((@nil Z))))) + 1 ) (c_string ((Znth (i) (rows) ((@nil Z))))) )
  **  ((( &( "len" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "words_size" ) )) # Int  |-> words_size_pre)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "max" ) )) # Ptr  |-> max)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "maxu" ) )) # Int  |-> maxu)
  **  (PtrArray.full words_pre words_size_pre ptrs )
  **  (row_stores_missing_i_158 ptrs rows i )
  **  (IntArray.full ( &( "seen" ) ) 256 (repeat_Z (0) (256)) )
|--
  “ ((string_length ((Znth (i) (rows) ((@nil Z))))) < INT_MAX) ”
.

Definition find_max_partial_solve_wit_4_aux := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (i: Z) (k: Z) (cur: Z) (max: Z) (best: Z) (maxu: Z) (PreH1 : (0 <= i)) (PreH2 : (i < words_size_pre)) (PreH3 : (k = 256)) (PreH4 : (cur = (Znth (i) (ptrs) (0)))) (PreH5 : (max = (Znth (best) (ptrs) (0)))) (PreH6 : (0 < words_size_pre)) (PreH7 : (words_size_pre < INT_MAX)) (PreH8 : ((Zlength (ptrs)) = words_size_pre)) (PreH9 : (problem_158_pre_z rows )) (PreH10 : (rows_well_formed_158 rows words_size_pre )) (PreH11 : (best_state_158 rows i best maxu )) ,
  (PtrArray.full words_pre words_size_pre ptrs )
  **  (row_stores_missing_i_158 ptrs rows i )
  **  (store_string cur (Znth (i) (rows) ((@nil Z))) )
  **  (IntArray.full ( &( "seen" ) ) 256 (repeat_Z (0) (256)) )
|--
  “ ((string_length ((Znth (i) (rows) ((@nil Z))))) < INT_MAX) ” 
  &&  “ (valid_string (Znth (i) (rows) ((@nil Z))) ) ” 
  &&  “ (0 <= ((string_length ((Znth (i) (rows) ((@nil Z))))) + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < words_size_pre) ” 
  &&  “ (k = 256) ” 
  &&  “ (cur = (Znth (i) (ptrs) (0))) ” 
  &&  “ (max = (Znth (best) (ptrs) (0))) ” 
  &&  “ (0 < words_size_pre) ” 
  &&  “ (words_size_pre < INT_MAX) ” 
  &&  “ ((Zlength (ptrs)) = words_size_pre) ” 
  &&  “ (problem_158_pre_z rows ) ” 
  &&  “ (rows_well_formed_158 rows words_size_pre ) ” 
  &&  “ (best_state_158 rows i best maxu ) ”
  &&  (store_string cur (Znth (i) (rows) ((@nil Z))) )
  **  (PtrArray.full words_pre words_size_pre ptrs )
  **  (row_stores_missing_i_158 ptrs rows i )
  **  (IntArray.full ( &( "seen" ) ) 256 (repeat_Z (0) (256)) )
.

Definition find_max_partial_solve_wit_4 := find_max_partial_solve_wit_4_pure -> find_max_partial_solve_wit_4_aux.

Definition find_max_partial_solve_wit_5 := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (seen_l: (@list Z)) (j: Z) (len: Z) (i: Z) (unique: Z) (ch: Z) (k: Z) (cur: Z) (max: Z) (best: Z) (maxu: Z) (PreH1 : (0 <= j)) (PreH2 : (j < len)) (PreH3 : (len = (string_length ((Znth (i) (rows) ((@nil Z))))))) (PreH4 : (0 <= unique)) (PreH5 : (unique <= j)) (PreH6 : (0 <= ch)) (PreH7 : (ch < 256)) (PreH8 : (ch = (Znth (j) ((Znth (i) (rows) ((@nil Z)))) (0)))) (PreH9 : (k = 256)) (PreH10 : (0 <= i)) (PreH11 : (i < words_size_pre)) (PreH12 : (cur = (Znth (i) (ptrs) (0)))) (PreH13 : (max = (Znth (best) (ptrs) (0)))) (PreH14 : (0 <= best)) (PreH15 : (best < words_size_pre)) (PreH16 : (0 < words_size_pre)) (PreH17 : (words_size_pre < INT_MAX)) (PreH18 : ((Zlength (ptrs)) = words_size_pre)) (PreH19 : (problem_158_pre_z rows )) (PreH20 : (rows_well_formed_158 rows words_size_pre )) (PreH21 : (best_state_158 rows i best maxu )) (PreH22 : (seen_state_158 (Znth (i) (rows) ((@nil Z))) j seen_l unique )) ,
  (PtrArray.full words_pre words_size_pre ptrs )
  **  (row_stores_missing_i_158 ptrs rows i )
  **  (store_string cur (Znth (i) (rows) ((@nil Z))) )
  **  (IntArray.full ( &( "seen" ) ) 256 seen_l )
|--
  “ (0 <= ((string_length ((Znth (i) (rows) ((@nil Z))))) + 1 )) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < len) ” 
  &&  “ (len = (string_length ((Znth (i) (rows) ((@nil Z)))))) ” 
  &&  “ (0 <= unique) ” 
  &&  “ (unique <= j) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch < 256) ” 
  &&  “ (ch = (Znth (j) ((Znth (i) (rows) ((@nil Z)))) (0))) ” 
  &&  “ (k = 256) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < words_size_pre) ” 
  &&  “ (cur = (Znth (i) (ptrs) (0))) ” 
  &&  “ (max = (Znth (best) (ptrs) (0))) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best < words_size_pre) ” 
  &&  “ (0 < words_size_pre) ” 
  &&  “ (words_size_pre < INT_MAX) ” 
  &&  “ ((Zlength (ptrs)) = words_size_pre) ” 
  &&  “ (problem_158_pre_z rows ) ” 
  &&  “ (rows_well_formed_158 rows words_size_pre ) ” 
  &&  “ (best_state_158 rows i best maxu ) ” 
  &&  “ (seen_state_158 (Znth (i) (rows) ((@nil Z))) j seen_l unique ) ”
  &&  (((( &( "seen" ) ) + (ch * sizeof(INT) ) )) # Int  |-> (Znth ch seen_l 0))
  **  (CharArray.full cur ((string_length ((Znth (i) (rows) ((@nil Z))))) + 1 ) (c_string ((Znth (i) (rows) ((@nil Z))))) )
  **  (IntArray.missing_i ( &( "seen" ) ) ch 0 256 seen_l )
  **  (PtrArray.full words_pre words_size_pre ptrs )
  **  (row_stores_missing_i_158 ptrs rows i )
.

Definition find_max_partial_solve_wit_6 := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (seen_l: (@list Z)) (j: Z) (len: Z) (i: Z) (unique: Z) (ch: Z) (k: Z) (cur: Z) (max: Z) (best: Z) (maxu: Z) (PreH1 : ((Znth ch seen_l 0) = 0)) (PreH2 : (0 <= ((string_length ((Znth (i) (rows) ((@nil Z))))) + 1 ))) (PreH3 : (0 <= j)) (PreH4 : (j < len)) (PreH5 : (len = (string_length ((Znth (i) (rows) ((@nil Z))))))) (PreH6 : (0 <= unique)) (PreH7 : (unique <= j)) (PreH8 : (0 <= ch)) (PreH9 : (ch < 256)) (PreH10 : (ch = (Znth (j) ((Znth (i) (rows) ((@nil Z)))) (0)))) (PreH11 : (k = 256)) (PreH12 : (0 <= i)) (PreH13 : (i < words_size_pre)) (PreH14 : (cur = (Znth (i) (ptrs) (0)))) (PreH15 : (max = (Znth (best) (ptrs) (0)))) (PreH16 : (0 <= best)) (PreH17 : (best < words_size_pre)) (PreH18 : (0 < words_size_pre)) (PreH19 : (words_size_pre < INT_MAX)) (PreH20 : ((Zlength (ptrs)) = words_size_pre)) (PreH21 : (problem_158_pre_z rows )) (PreH22 : (rows_well_formed_158 rows words_size_pre )) (PreH23 : (best_state_158 rows i best maxu )) (PreH24 : (seen_state_158 (Znth (i) (rows) ((@nil Z))) j seen_l unique )) ,
  (IntArray.full ( &( "seen" ) ) 256 seen_l )
  **  (CharArray.full cur ((string_length ((Znth (i) (rows) ((@nil Z))))) + 1 ) (c_string ((Znth (i) (rows) ((@nil Z))))) )
  **  (PtrArray.full words_pre words_size_pre ptrs )
  **  (row_stores_missing_i_158 ptrs rows i )
|--
  “ ((Znth ch seen_l 0) = 0) ” 
  &&  “ (0 <= ((string_length ((Znth (i) (rows) ((@nil Z))))) + 1 )) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < len) ” 
  &&  “ (len = (string_length ((Znth (i) (rows) ((@nil Z)))))) ” 
  &&  “ (0 <= unique) ” 
  &&  “ (unique <= j) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch < 256) ” 
  &&  “ (ch = (Znth (j) ((Znth (i) (rows) ((@nil Z)))) (0))) ” 
  &&  “ (k = 256) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < words_size_pre) ” 
  &&  “ (cur = (Znth (i) (ptrs) (0))) ” 
  &&  “ (max = (Znth (best) (ptrs) (0))) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best < words_size_pre) ” 
  &&  “ (0 < words_size_pre) ” 
  &&  “ (words_size_pre < INT_MAX) ” 
  &&  “ ((Zlength (ptrs)) = words_size_pre) ” 
  &&  “ (problem_158_pre_z rows ) ” 
  &&  “ (rows_well_formed_158 rows words_size_pre ) ” 
  &&  “ (best_state_158 rows i best maxu ) ” 
  &&  “ (seen_state_158 (Znth (i) (rows) ((@nil Z))) j seen_l unique ) ”
  &&  (((( &( "seen" ) ) + (ch * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i ( &( "seen" ) ) ch 0 256 seen_l )
  **  (CharArray.full cur ((string_length ((Znth (i) (rows) ((@nil Z))))) + 1 ) (c_string ((Znth (i) (rows) ((@nil Z))))) )
  **  (PtrArray.full words_pre words_size_pre ptrs )
  **  (row_stores_missing_i_158 ptrs rows i )
.

Definition find_max_partial_solve_wit_7_pure := 
(
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (seen_l: (@list Z)) (best: Z) (i: Z) (j: Z) (len: Z) (k: Z) (cur: Z) (max: Z) (better: Z) (cmp: Z) (unique: Z) (maxu: Z) (PreH1 : (0 <= best)) (PreH2 : (best < i)) (PreH3 : (i < words_size_pre)) (PreH4 : (j = len)) (PreH5 : (k = 256)) (PreH6 : (cur = (Znth (i) (ptrs) (0)))) (PreH7 : (max = (Znth (best) (ptrs) (0)))) (PreH8 : (better = 0)) (PreH9 : (cmp = 0)) (PreH10 : (unique = (unique_count_z_158 ((Znth (i) (rows) ((@nil Z))))))) (PreH11 : (unique = maxu)) (PreH12 : (0 < words_size_pre)) (PreH13 : (words_size_pre < INT_MAX)) (PreH14 : ((Zlength (ptrs)) = words_size_pre)) (PreH15 : (problem_158_pre_z rows )) (PreH16 : (rows_well_formed_158 rows words_size_pre )) (PreH17 : (best_state_158 rows i best maxu )) ,
  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "words_size" ) )) # Int  |-> words_size_pre)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "max" ) )) # Ptr  |-> max)
  **  ((( &( "better" ) )) # Int  |-> better)
  **  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "unique" ) )) # Int  |-> unique)
  **  ((( &( "maxu" ) )) # Int  |-> maxu)
  **  (PtrArray.full words_pre words_size_pre ptrs )
  **  (row_stores_missing_two_158 ptrs rows best i )
  **  (store_string max (Znth (best) (rows) ((@nil Z))) )
  **  (store_string cur (Znth (i) (rows) ((@nil Z))) )
  **  (IntArray.full ( &( "seen" ) ) 256 seen_l )
|--
  “ ((string_length ((Znth (best) (rows) ((@nil Z))))) < INT_MAX) ” 
  &&  “ ((string_length ((Znth (i) (rows) ((@nil Z))))) < INT_MAX) ” 
  &&  “ (valid_string (Znth (best) (rows) ((@nil Z))) ) ” 
  &&  “ (valid_string (Znth (i) (rows) ((@nil Z))) ) ”
) \/
(
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (seen_l: (@list Z)) (best: Z) (i: Z) (j: Z) (len: Z) (k: Z) (cur: Z) (max: Z) (better: Z) (cmp: Z) (unique: Z) (maxu: Z) (PreH1 : (maxu <= INT_MAX)) (PreH2 : (unique <= INT_MAX)) (PreH3 : (cmp <= INT_MAX)) (PreH4 : (better <= INT_MAX)) (PreH5 : (words_size_pre <= INT_MAX)) (PreH6 : (k <= INT_MAX)) (PreH7 : (len <= INT_MAX)) (PreH8 : (j <= INT_MAX)) (PreH9 : (i <= INT_MAX)) (PreH10 : (best <= INT_MAX)) (PreH11 : (maxu >= INT_MIN)) (PreH12 : (unique >= INT_MIN)) (PreH13 : (cmp >= INT_MIN)) (PreH14 : (better >= INT_MIN)) (PreH15 : (words_size_pre >= INT_MIN)) (PreH16 : (k >= INT_MIN)) (PreH17 : (len >= INT_MIN)) (PreH18 : (j >= INT_MIN)) (PreH19 : (i >= INT_MIN)) (PreH20 : (best >= INT_MIN)) (PreH21 : (0 <= ((string_length ((Znth (i) (rows) ((@nil Z))))) + 1 ))) (PreH22 : (0 <= ((string_length ((Znth (best) (rows) ((@nil Z))))) + 1 ))) (PreH23 : (0 <= best)) (PreH24 : (best < i)) (PreH25 : (i < words_size_pre)) (PreH26 : (j = len)) (PreH27 : (k = 256)) (PreH28 : (cur = (Znth (i) (ptrs) (0)))) (PreH29 : (max = (Znth (best) (ptrs) (0)))) (PreH30 : (better = 0)) (PreH31 : (cmp = 0)) (PreH32 : (unique = (unique_count_z_158 ((Znth (i) (rows) ((@nil Z))))))) (PreH33 : (unique = maxu)) (PreH34 : (0 < words_size_pre)) (PreH35 : (words_size_pre < INT_MAX)) (PreH36 : ((Zlength (ptrs)) = words_size_pre)) (PreH37 : (problem_158_pre_z rows )) (PreH38 : (rows_well_formed_158 rows words_size_pre )) (PreH39 : (best_state_158 rows i best maxu )) ,
  (CharArray.full cur ((string_length ((Znth (i) (rows) ((@nil Z))))) + 1 ) (c_string ((Znth (i) (rows) ((@nil Z))))) )
  **  (CharArray.full max ((string_length ((Znth (best) (rows) ((@nil Z))))) + 1 ) (c_string ((Znth (best) (rows) ((@nil Z))))) )
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "words_size" ) )) # Int  |-> words_size_pre)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "max" ) )) # Ptr  |-> max)
  **  ((( &( "better" ) )) # Int  |-> better)
  **  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "unique" ) )) # Int  |-> unique)
  **  ((( &( "maxu" ) )) # Int  |-> maxu)
  **  (PtrArray.full words_pre words_size_pre ptrs )
  **  (row_stores_missing_two_158 ptrs rows best i )
  **  (IntArray.full ( &( "seen" ) ) 256 seen_l )
|--
  “ (valid_string (Znth (i) (rows) ((@nil Z))) ) ” 
  &&  “ (valid_string (Znth (best) (rows) ((@nil Z))) ) ” 
  &&  “ ((string_length ((Znth (i) (rows) ((@nil Z))))) < INT_MAX) ” 
  &&  “ ((string_length ((Znth (best) (rows) ((@nil Z))))) < INT_MAX) ”
).

Definition find_max_partial_solve_wit_7_pure_split_goal_1 := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (seen_l: (@list Z)) (best: Z) (i: Z) (j: Z) (len: Z) (k: Z) (cur: Z) (max: Z) (better: Z) (cmp: Z) (unique: Z) (maxu: Z) (PreH1 : (maxu <= INT_MAX)) (PreH2 : (unique <= INT_MAX)) (PreH3 : (cmp <= INT_MAX)) (PreH4 : (better <= INT_MAX)) (PreH5 : (words_size_pre <= INT_MAX)) (PreH6 : (k <= INT_MAX)) (PreH7 : (len <= INT_MAX)) (PreH8 : (j <= INT_MAX)) (PreH9 : (i <= INT_MAX)) (PreH10 : (best <= INT_MAX)) (PreH11 : (maxu >= INT_MIN)) (PreH12 : (unique >= INT_MIN)) (PreH13 : (cmp >= INT_MIN)) (PreH14 : (better >= INT_MIN)) (PreH15 : (words_size_pre >= INT_MIN)) (PreH16 : (k >= INT_MIN)) (PreH17 : (len >= INT_MIN)) (PreH18 : (j >= INT_MIN)) (PreH19 : (i >= INT_MIN)) (PreH20 : (best >= INT_MIN)) (PreH21 : (0 <= ((string_length ((Znth (i) (rows) ((@nil Z))))) + 1 ))) (PreH22 : (0 <= ((string_length ((Znth (best) (rows) ((@nil Z))))) + 1 ))) (PreH23 : (0 <= best)) (PreH24 : (best < i)) (PreH25 : (i < words_size_pre)) (PreH26 : (j = len)) (PreH27 : (k = 256)) (PreH28 : (cur = (Znth (i) (ptrs) (0)))) (PreH29 : (max = (Znth (best) (ptrs) (0)))) (PreH30 : (better = 0)) (PreH31 : (cmp = 0)) (PreH32 : (unique = (unique_count_z_158 ((Znth (i) (rows) ((@nil Z))))))) (PreH33 : (unique = maxu)) (PreH34 : (0 < words_size_pre)) (PreH35 : (words_size_pre < INT_MAX)) (PreH36 : ((Zlength (ptrs)) = words_size_pre)) (PreH37 : (problem_158_pre_z rows )) (PreH38 : (rows_well_formed_158 rows words_size_pre )) (PreH39 : (best_state_158 rows i best maxu )) ,
  (CharArray.full cur ((string_length ((Znth (i) (rows) ((@nil Z))))) + 1 ) (c_string ((Znth (i) (rows) ((@nil Z))))) )
  **  (CharArray.full max ((string_length ((Znth (best) (rows) ((@nil Z))))) + 1 ) (c_string ((Znth (best) (rows) ((@nil Z))))) )
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "words_size" ) )) # Int  |-> words_size_pre)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "max" ) )) # Ptr  |-> max)
  **  ((( &( "better" ) )) # Int  |-> better)
  **  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "unique" ) )) # Int  |-> unique)
  **  ((( &( "maxu" ) )) # Int  |-> maxu)
  **  (PtrArray.full words_pre words_size_pre ptrs )
  **  (row_stores_missing_two_158 ptrs rows best i )
  **  (IntArray.full ( &( "seen" ) ) 256 seen_l )
|--
  “ (valid_string (Znth (i) (rows) ((@nil Z))) ) ”
.

Definition find_max_partial_solve_wit_7_pure_split_goal_2 := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (seen_l: (@list Z)) (best: Z) (i: Z) (j: Z) (len: Z) (k: Z) (cur: Z) (max: Z) (better: Z) (cmp: Z) (unique: Z) (maxu: Z) (PreH1 : (maxu <= INT_MAX)) (PreH2 : (unique <= INT_MAX)) (PreH3 : (cmp <= INT_MAX)) (PreH4 : (better <= INT_MAX)) (PreH5 : (words_size_pre <= INT_MAX)) (PreH6 : (k <= INT_MAX)) (PreH7 : (len <= INT_MAX)) (PreH8 : (j <= INT_MAX)) (PreH9 : (i <= INT_MAX)) (PreH10 : (best <= INT_MAX)) (PreH11 : (maxu >= INT_MIN)) (PreH12 : (unique >= INT_MIN)) (PreH13 : (cmp >= INT_MIN)) (PreH14 : (better >= INT_MIN)) (PreH15 : (words_size_pre >= INT_MIN)) (PreH16 : (k >= INT_MIN)) (PreH17 : (len >= INT_MIN)) (PreH18 : (j >= INT_MIN)) (PreH19 : (i >= INT_MIN)) (PreH20 : (best >= INT_MIN)) (PreH21 : (0 <= ((string_length ((Znth (i) (rows) ((@nil Z))))) + 1 ))) (PreH22 : (0 <= ((string_length ((Znth (best) (rows) ((@nil Z))))) + 1 ))) (PreH23 : (0 <= best)) (PreH24 : (best < i)) (PreH25 : (i < words_size_pre)) (PreH26 : (j = len)) (PreH27 : (k = 256)) (PreH28 : (cur = (Znth (i) (ptrs) (0)))) (PreH29 : (max = (Znth (best) (ptrs) (0)))) (PreH30 : (better = 0)) (PreH31 : (cmp = 0)) (PreH32 : (unique = (unique_count_z_158 ((Znth (i) (rows) ((@nil Z))))))) (PreH33 : (unique = maxu)) (PreH34 : (0 < words_size_pre)) (PreH35 : (words_size_pre < INT_MAX)) (PreH36 : ((Zlength (ptrs)) = words_size_pre)) (PreH37 : (problem_158_pre_z rows )) (PreH38 : (rows_well_formed_158 rows words_size_pre )) (PreH39 : (best_state_158 rows i best maxu )) ,
  (CharArray.full cur ((string_length ((Znth (i) (rows) ((@nil Z))))) + 1 ) (c_string ((Znth (i) (rows) ((@nil Z))))) )
  **  (CharArray.full max ((string_length ((Znth (best) (rows) ((@nil Z))))) + 1 ) (c_string ((Znth (best) (rows) ((@nil Z))))) )
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "words_size" ) )) # Int  |-> words_size_pre)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "max" ) )) # Ptr  |-> max)
  **  ((( &( "better" ) )) # Int  |-> better)
  **  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "unique" ) )) # Int  |-> unique)
  **  ((( &( "maxu" ) )) # Int  |-> maxu)
  **  (PtrArray.full words_pre words_size_pre ptrs )
  **  (row_stores_missing_two_158 ptrs rows best i )
  **  (IntArray.full ( &( "seen" ) ) 256 seen_l )
|--
  “ (valid_string (Znth (best) (rows) ((@nil Z))) ) ”
.

Definition find_max_partial_solve_wit_7_pure_split_goal_3 := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (seen_l: (@list Z)) (best: Z) (i: Z) (j: Z) (len: Z) (k: Z) (cur: Z) (max: Z) (better: Z) (cmp: Z) (unique: Z) (maxu: Z) (PreH1 : (maxu <= INT_MAX)) (PreH2 : (unique <= INT_MAX)) (PreH3 : (cmp <= INT_MAX)) (PreH4 : (better <= INT_MAX)) (PreH5 : (words_size_pre <= INT_MAX)) (PreH6 : (k <= INT_MAX)) (PreH7 : (len <= INT_MAX)) (PreH8 : (j <= INT_MAX)) (PreH9 : (i <= INT_MAX)) (PreH10 : (best <= INT_MAX)) (PreH11 : (maxu >= INT_MIN)) (PreH12 : (unique >= INT_MIN)) (PreH13 : (cmp >= INT_MIN)) (PreH14 : (better >= INT_MIN)) (PreH15 : (words_size_pre >= INT_MIN)) (PreH16 : (k >= INT_MIN)) (PreH17 : (len >= INT_MIN)) (PreH18 : (j >= INT_MIN)) (PreH19 : (i >= INT_MIN)) (PreH20 : (best >= INT_MIN)) (PreH21 : (0 <= ((string_length ((Znth (i) (rows) ((@nil Z))))) + 1 ))) (PreH22 : (0 <= ((string_length ((Znth (best) (rows) ((@nil Z))))) + 1 ))) (PreH23 : (0 <= best)) (PreH24 : (best < i)) (PreH25 : (i < words_size_pre)) (PreH26 : (j = len)) (PreH27 : (k = 256)) (PreH28 : (cur = (Znth (i) (ptrs) (0)))) (PreH29 : (max = (Znth (best) (ptrs) (0)))) (PreH30 : (better = 0)) (PreH31 : (cmp = 0)) (PreH32 : (unique = (unique_count_z_158 ((Znth (i) (rows) ((@nil Z))))))) (PreH33 : (unique = maxu)) (PreH34 : (0 < words_size_pre)) (PreH35 : (words_size_pre < INT_MAX)) (PreH36 : ((Zlength (ptrs)) = words_size_pre)) (PreH37 : (problem_158_pre_z rows )) (PreH38 : (rows_well_formed_158 rows words_size_pre )) (PreH39 : (best_state_158 rows i best maxu )) ,
  (CharArray.full cur ((string_length ((Znth (i) (rows) ((@nil Z))))) + 1 ) (c_string ((Znth (i) (rows) ((@nil Z))))) )
  **  (CharArray.full max ((string_length ((Znth (best) (rows) ((@nil Z))))) + 1 ) (c_string ((Znth (best) (rows) ((@nil Z))))) )
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "words_size" ) )) # Int  |-> words_size_pre)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "max" ) )) # Ptr  |-> max)
  **  ((( &( "better" ) )) # Int  |-> better)
  **  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "unique" ) )) # Int  |-> unique)
  **  ((( &( "maxu" ) )) # Int  |-> maxu)
  **  (PtrArray.full words_pre words_size_pre ptrs )
  **  (row_stores_missing_two_158 ptrs rows best i )
  **  (IntArray.full ( &( "seen" ) ) 256 seen_l )
|--
  “ ((string_length ((Znth (i) (rows) ((@nil Z))))) < INT_MAX) ”
.

Definition find_max_partial_solve_wit_7_pure_split_goal_4 := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (seen_l: (@list Z)) (best: Z) (i: Z) (j: Z) (len: Z) (k: Z) (cur: Z) (max: Z) (better: Z) (cmp: Z) (unique: Z) (maxu: Z) (PreH1 : (maxu <= INT_MAX)) (PreH2 : (unique <= INT_MAX)) (PreH3 : (cmp <= INT_MAX)) (PreH4 : (better <= INT_MAX)) (PreH5 : (words_size_pre <= INT_MAX)) (PreH6 : (k <= INT_MAX)) (PreH7 : (len <= INT_MAX)) (PreH8 : (j <= INT_MAX)) (PreH9 : (i <= INT_MAX)) (PreH10 : (best <= INT_MAX)) (PreH11 : (maxu >= INT_MIN)) (PreH12 : (unique >= INT_MIN)) (PreH13 : (cmp >= INT_MIN)) (PreH14 : (better >= INT_MIN)) (PreH15 : (words_size_pre >= INT_MIN)) (PreH16 : (k >= INT_MIN)) (PreH17 : (len >= INT_MIN)) (PreH18 : (j >= INT_MIN)) (PreH19 : (i >= INT_MIN)) (PreH20 : (best >= INT_MIN)) (PreH21 : (0 <= ((string_length ((Znth (i) (rows) ((@nil Z))))) + 1 ))) (PreH22 : (0 <= ((string_length ((Znth (best) (rows) ((@nil Z))))) + 1 ))) (PreH23 : (0 <= best)) (PreH24 : (best < i)) (PreH25 : (i < words_size_pre)) (PreH26 : (j = len)) (PreH27 : (k = 256)) (PreH28 : (cur = (Znth (i) (ptrs) (0)))) (PreH29 : (max = (Znth (best) (ptrs) (0)))) (PreH30 : (better = 0)) (PreH31 : (cmp = 0)) (PreH32 : (unique = (unique_count_z_158 ((Znth (i) (rows) ((@nil Z))))))) (PreH33 : (unique = maxu)) (PreH34 : (0 < words_size_pre)) (PreH35 : (words_size_pre < INT_MAX)) (PreH36 : ((Zlength (ptrs)) = words_size_pre)) (PreH37 : (problem_158_pre_z rows )) (PreH38 : (rows_well_formed_158 rows words_size_pre )) (PreH39 : (best_state_158 rows i best maxu )) ,
  (CharArray.full cur ((string_length ((Znth (i) (rows) ((@nil Z))))) + 1 ) (c_string ((Znth (i) (rows) ((@nil Z))))) )
  **  (CharArray.full max ((string_length ((Znth (best) (rows) ((@nil Z))))) + 1 ) (c_string ((Znth (best) (rows) ((@nil Z))))) )
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "words_size" ) )) # Int  |-> words_size_pre)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "max" ) )) # Ptr  |-> max)
  **  ((( &( "better" ) )) # Int  |-> better)
  **  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "unique" ) )) # Int  |-> unique)
  **  ((( &( "maxu" ) )) # Int  |-> maxu)
  **  (PtrArray.full words_pre words_size_pre ptrs )
  **  (row_stores_missing_two_158 ptrs rows best i )
  **  (IntArray.full ( &( "seen" ) ) 256 seen_l )
|--
  “ ((string_length ((Znth (best) (rows) ((@nil Z))))) < INT_MAX) ”
.

Definition find_max_partial_solve_wit_7_aux := 
forall (words_size_pre: Z) (words_pre: Z) (rows: (@list (@list Z))) (ptrs: (@list Z)) (seen_l: (@list Z)) (best: Z) (i: Z) (j: Z) (len: Z) (k: Z) (cur: Z) (max: Z) (better: Z) (cmp: Z) (unique: Z) (maxu: Z) (PreH1 : (0 <= best)) (PreH2 : (best < i)) (PreH3 : (i < words_size_pre)) (PreH4 : (j = len)) (PreH5 : (k = 256)) (PreH6 : (cur = (Znth (i) (ptrs) (0)))) (PreH7 : (max = (Znth (best) (ptrs) (0)))) (PreH8 : (better = 0)) (PreH9 : (cmp = 0)) (PreH10 : (unique = (unique_count_z_158 ((Znth (i) (rows) ((@nil Z))))))) (PreH11 : (unique = maxu)) (PreH12 : (0 < words_size_pre)) (PreH13 : (words_size_pre < INT_MAX)) (PreH14 : ((Zlength (ptrs)) = words_size_pre)) (PreH15 : (problem_158_pre_z rows )) (PreH16 : (rows_well_formed_158 rows words_size_pre )) (PreH17 : (best_state_158 rows i best maxu )) ,
  (PtrArray.full words_pre words_size_pre ptrs )
  **  (row_stores_missing_two_158 ptrs rows best i )
  **  (store_string max (Znth (best) (rows) ((@nil Z))) )
  **  (store_string cur (Znth (i) (rows) ((@nil Z))) )
  **  (IntArray.full ( &( "seen" ) ) 256 seen_l )
|--
  “ ((string_length ((Znth (best) (rows) ((@nil Z))))) < INT_MAX) ” 
  &&  “ ((string_length ((Znth (i) (rows) ((@nil Z))))) < INT_MAX) ” 
  &&  “ (valid_string (Znth (best) (rows) ((@nil Z))) ) ” 
  &&  “ (valid_string (Znth (i) (rows) ((@nil Z))) ) ” 
  &&  “ (0 <= ((string_length ((Znth (i) (rows) ((@nil Z))))) + 1 )) ” 
  &&  “ (0 <= ((string_length ((Znth (best) (rows) ((@nil Z))))) + 1 )) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best < i) ” 
  &&  “ (i < words_size_pre) ” 
  &&  “ (j = len) ” 
  &&  “ (k = 256) ” 
  &&  “ (cur = (Znth (i) (ptrs) (0))) ” 
  &&  “ (max = (Znth (best) (ptrs) (0))) ” 
  &&  “ (better = 0) ” 
  &&  “ (cmp = 0) ” 
  &&  “ (unique = (unique_count_z_158 ((Znth (i) (rows) ((@nil Z)))))) ” 
  &&  “ (unique = maxu) ” 
  &&  “ (0 < words_size_pre) ” 
  &&  “ (words_size_pre < INT_MAX) ” 
  &&  “ ((Zlength (ptrs)) = words_size_pre) ” 
  &&  “ (problem_158_pre_z rows ) ” 
  &&  “ (rows_well_formed_158 rows words_size_pre ) ” 
  &&  “ (best_state_158 rows i best maxu ) ”
  &&  (store_string cur (Znth (i) (rows) ((@nil Z))) )
  **  (store_string max (Znth (best) (rows) ((@nil Z))) )
  **  (PtrArray.full words_pre words_size_pre ptrs )
  **  (row_stores_missing_two_158 ptrs rows best i )
  **  (IntArray.full ( &( "seen" ) ) 256 seen_l )
.

Definition find_max_partial_solve_wit_7 := find_max_partial_solve_wit_7_pure -> find_max_partial_solve_wit_7_aux.

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
Axiom proof_of_find_max_entail_wit_1 : find_max_entail_wit_1.
Axiom proof_of_find_max_entail_wit_2 : find_max_entail_wit_2.
Axiom proof_of_find_max_entail_wit_3 : find_max_entail_wit_3.
Axiom proof_of_find_max_entail_wit_4 : find_max_entail_wit_4.
Axiom proof_of_find_max_entail_wit_5 : find_max_entail_wit_5.
Axiom proof_of_find_max_entail_wit_6 : find_max_entail_wit_6.
Axiom proof_of_find_max_entail_wit_7_1 : find_max_entail_wit_7_1.
Axiom proof_of_find_max_entail_wit_7_2 : find_max_entail_wit_7_2.
Axiom proof_of_find_max_entail_wit_8 : find_max_entail_wit_8.
Axiom proof_of_find_max_entail_wit_9 : find_max_entail_wit_9.
Axiom proof_of_find_max_entail_wit_10 : find_max_entail_wit_10.
Axiom proof_of_find_max_entail_wit_11_1 : find_max_entail_wit_11_1.
Axiom proof_of_find_max_entail_wit_11_2 : find_max_entail_wit_11_2.
Axiom proof_of_find_max_entail_wit_11_3 : find_max_entail_wit_11_3.
Axiom proof_of_find_max_entail_wit_11_4 : find_max_entail_wit_11_4.
Axiom proof_of_find_max_entail_wit_11_5 : find_max_entail_wit_11_5.
Axiom proof_of_find_max_entail_wit_12 : find_max_entail_wit_12.
Axiom proof_of_find_max_return_wit_1 : find_max_return_wit_1.
Axiom proof_of_find_max_partial_solve_wit_1 : find_max_partial_solve_wit_1.
Axiom proof_of_find_max_partial_solve_wit_2 : find_max_partial_solve_wit_2.
Axiom proof_of_find_max_partial_solve_wit_3 : find_max_partial_solve_wit_3.
Axiom proof_of_find_max_partial_solve_wit_4_pure : find_max_partial_solve_wit_4_pure.
Axiom proof_of_find_max_partial_solve_wit_4 : find_max_partial_solve_wit_4.
Axiom proof_of_find_max_partial_solve_wit_5 : find_max_partial_solve_wit_5.
Axiom proof_of_find_max_partial_solve_wit_6 : find_max_partial_solve_wit_6.
Axiom proof_of_find_max_partial_solve_wit_7_pure : find_max_partial_solve_wit_7_pure.
Axiom proof_of_find_max_partial_solve_wit_7 : find_max_partial_solve_wit_7.

End VC_Correct.
