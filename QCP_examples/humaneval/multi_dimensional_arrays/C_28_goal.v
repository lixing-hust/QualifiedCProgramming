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
Require Import coins_28.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import ptr_array2_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import ptr_array2_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_proof.
Require Import string_strategy_goal.
Require Import string_strategy_proof.

(*----- Function concatenate -----*)

Definition concatenate_safety_wit_1 := 
forall (strings_size_pre: Z) (strings_pre: Z) (rows: (@list (@list Z))) (PreH1 : (0 <= strings_size_pre)) (PreH2 : (strings_size_pre <= 100)) (PreH3 : (rows_well_formed_28 rows strings_size_pre )) (PreH4 : forall (p: Z) , (((0 <= p) /\ (p <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p)) + 1 ) < INT_MAX))) (PreH5 : (problem_28_pre_z rows )) ,
  ((( &( "total" ) )) # Int  |->_)
  **  ((( &( "strings_size" ) )) # Int  |-> strings_size_pre)
  **  ((( &( "strings" ) )) # Ptr  |-> strings_pre)
  **  (CharPtrArray2.full strings_pre strings_size_pre rows )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition concatenate_safety_wit_2 := 
forall (strings_size_pre: Z) (strings_pre: Z) (rows: (@list (@list Z))) (PreH1 : (0 <= strings_size_pre)) (PreH2 : (strings_size_pre <= 100)) (PreH3 : (rows_well_formed_28 rows strings_size_pre )) (PreH4 : forall (p: Z) , (((0 <= p) /\ (p <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p)) + 1 ) < INT_MAX))) (PreH5 : (problem_28_pre_z rows )) ,
  ((( &( "out" ) )) # Ptr  |->_)
  **  ((( &( "total" ) )) # Int  |-> 1)
  **  ((( &( "strings_size" ) )) # Int  |-> strings_size_pre)
  **  ((( &( "strings" ) )) # Ptr  |-> strings_pre)
  **  (CharPtrArray2.full strings_pre strings_size_pre rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition concatenate_safety_wit_3 := 
forall (strings_size_pre: Z) (strings_pre: Z) (rows: (@list (@list Z))) (PreH1 : (0 <= strings_size_pre)) (PreH2 : (strings_size_pre <= 100)) (PreH3 : (rows_well_formed_28 rows strings_size_pre )) (PreH4 : forall (p: Z) , (((0 <= p) /\ (p <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p)) + 1 ) < INT_MAX))) (PreH5 : (problem_28_pre_z rows )) ,
  ((( &( "k" ) )) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> 0)
  **  ((( &( "total" ) )) # Int  |-> 1)
  **  ((( &( "strings_size" ) )) # Int  |-> strings_size_pre)
  **  ((( &( "strings" ) )) # Ptr  |-> strings_pre)
  **  (CharPtrArray2.full strings_pre strings_size_pre rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition concatenate_safety_wit_4 := 
forall (strings_size_pre: Z) (strings_pre: Z) (rows: (@list (@list Z))) (PreH1 : (0 <= strings_size_pre)) (PreH2 : (strings_size_pre <= 100)) (PreH3 : (rows_well_formed_28 rows strings_size_pre )) (PreH4 : forall (p: Z) , (((0 <= p) /\ (p <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p)) + 1 ) < INT_MAX))) (PreH5 : (problem_28_pre_z rows )) ,
  ((( &( "len0" ) )) # Int  |->_)
  **  ((( &( "k" ) )) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> 0)
  **  ((( &( "total" ) )) # Int  |-> 1)
  **  ((( &( "strings_size" ) )) # Int  |-> strings_size_pre)
  **  ((( &( "strings" ) )) # Ptr  |-> strings_pre)
  **  (CharPtrArray2.full strings_pre strings_size_pre rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition concatenate_safety_wit_5 := 
forall (strings_size_pre: Z) (strings_pre: Z) (rows: (@list (@list Z))) (PreH1 : (0 <= strings_size_pre)) (PreH2 : (strings_size_pre <= 100)) (PreH3 : (rows_well_formed_28 rows strings_size_pre )) (PreH4 : forall (p: Z) , (((0 <= p) /\ (p <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p)) + 1 ) < INT_MAX))) (PreH5 : (problem_28_pre_z rows )) ,
  ((( &( "len" ) )) # Int  |->_)
  **  ((( &( "len0" ) )) # Int  |-> 0)
  **  ((( &( "k" ) )) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> 0)
  **  ((( &( "total" ) )) # Int  |-> 1)
  **  ((( &( "strings_size" ) )) # Int  |-> strings_size_pre)
  **  ((( &( "strings" ) )) # Ptr  |-> strings_pre)
  **  (CharPtrArray2.full strings_pre strings_size_pre rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition concatenate_safety_wit_6 := 
forall (strings_size_pre: Z) (strings_pre: Z) (rows: (@list (@list Z))) (PreH1 : (0 <= strings_size_pre)) (PreH2 : (strings_size_pre <= 100)) (PreH3 : (rows_well_formed_28 rows strings_size_pre )) (PreH4 : forall (p: Z) , (((0 <= p) /\ (p <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p)) + 1 ) < INT_MAX))) (PreH5 : (problem_28_pre_z rows )) ,
  ((( &( "cur" ) )) # Ptr  |->_)
  **  ((( &( "len" ) )) # Int  |-> 0)
  **  ((( &( "len0" ) )) # Int  |-> 0)
  **  ((( &( "k" ) )) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> 0)
  **  ((( &( "total" ) )) # Int  |-> 1)
  **  ((( &( "strings_size" ) )) # Int  |-> strings_size_pre)
  **  ((( &( "strings" ) )) # Ptr  |-> strings_pre)
  **  (CharPtrArray2.full strings_pre strings_size_pre rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition concatenate_safety_wit_7 := 
forall (strings_size_pre: Z) (strings_pre: Z) (rows: (@list (@list Z))) (PreH1 : (0 <= strings_size_pre)) (PreH2 : (strings_size_pre <= 100)) (PreH3 : (rows_well_formed_28 rows strings_size_pre )) (PreH4 : forall (p: Z) , (((0 <= p) /\ (p <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p)) + 1 ) < INT_MAX))) (PreH5 : (problem_28_pre_z rows )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Ptr  |-> 0)
  **  ((( &( "len" ) )) # Int  |-> 0)
  **  ((( &( "len0" ) )) # Int  |-> 0)
  **  ((( &( "k" ) )) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> 0)
  **  ((( &( "total" ) )) # Int  |-> 1)
  **  ((( &( "strings_size" ) )) # Int  |-> strings_size_pre)
  **  ((( &( "strings" ) )) # Ptr  |-> strings_pre)
  **  (CharPtrArray2.full strings_pre strings_size_pre rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition concatenate_safety_wit_8 := 
forall (strings_size_pre: Z) (strings_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (i: Z) (out: Z) (k: Z) (len0: Z) (total: Z) (len: Z) (PreH1 : (0 <= i)) (PreH2 : (i < strings_size_pre)) (PreH3 : (0 <= strings_size_pre)) (PreH4 : (strings_size_pre <= 100)) (PreH5 : (out = 0)) (PreH6 : (k = 0)) (PreH7 : (len0 = (row_len_z_28 ((Znth (i) (rows) ((@nil Z))))))) (PreH8 : ((total + len0 ) < INT_MAX)) (PreH9 : (0 <= len0)) (PreH10 : (len0 < INT_MAX)) (PreH11 : (0 <= len)) (PreH12 : (len < INT_MAX)) (PreH13 : (rows_well_formed_28 rows strings_size_pre )) (PreH14 : forall (p: Z) , (((0 <= p) /\ (p <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p)) + 1 ) < INT_MAX))) (PreH15 : (problem_28_pre_z rows )) (PreH16 : (total_prefix_state_28 rows i total )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "strings_size" ) )) # Int  |-> strings_size_pre)
  **  ((( &( "strings" ) )) # Ptr  |-> strings_pre)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "len0" ) )) # Int  |-> len0)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  (CharPtrArray2.missing_i strings_pre strings_size_pre i row_ptr rows )
  **  (((strings_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
|--
  “ ((total + len0 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (total + len0 )) ”
.

Definition concatenate_safety_wit_9 := 
forall (strings_size_pre: Z) (strings_pre: Z) (rows: (@list (@list Z))) (i: Z) (out: Z) (k: Z) (cur: Z) (len0: Z) (len: Z) (total: Z) (PreH1 : (0 <= i)) (PreH2 : (i < strings_size_pre)) (PreH3 : (0 <= strings_size_pre)) (PreH4 : (strings_size_pre <= 100)) (PreH5 : (out = 0)) (PreH6 : (k = 0)) (PreH7 : (len0 = (row_len_z_28 ((Znth (i) (rows) ((@nil Z))))))) (PreH8 : (0 <= len0)) (PreH9 : (len0 < INT_MAX)) (PreH10 : (0 <= len)) (PreH11 : (len < INT_MAX)) (PreH12 : (rows_well_formed_28 rows strings_size_pre )) (PreH13 : forall (p: Z) , (((0 <= p) /\ (p <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p)) + 1 ) < INT_MAX))) (PreH14 : (problem_28_pre_z rows )) (PreH15 : (total_prefix_state_28 rows (i + 1 ) total )) (PreH16 : (0 < total)) (PreH17 : (total < INT_MAX)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "strings_size" ) )) # Int  |-> strings_size_pre)
  **  ((( &( "strings" ) )) # Ptr  |-> strings_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "len0" ) )) # Int  |-> len0)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  (CharPtrArray2.full strings_pre strings_size_pre rows )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition concatenate_safety_wit_10 := 
forall (strings_size_pre: Z) (strings_pre: Z) (rows: (@list (@list Z))) (total: Z) (len: Z) (len0: Z) (cur: Z) (k: Z) (out: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (i >= strings_size_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= strings_size_pre)) (PreH5 : (0 <= strings_size_pre)) (PreH6 : (strings_size_pre <= 100)) (PreH7 : (out = 0)) (PreH8 : (k = 0)) (PreH9 : (0 <= len0)) (PreH10 : (len0 < INT_MAX)) (PreH11 : (0 <= len)) (PreH12 : (len < INT_MAX)) (PreH13 : (rows_well_formed_28 rows strings_size_pre )) (PreH14 : forall (p: Z) , (((0 <= p) /\ (p <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p)) + 1 ) < INT_MAX))) (PreH15 : (problem_28_pre_z rows )) (PreH16 : (total_prefix_state_28 rows i total )) (PreH17 : (0 < total)) (PreH18 : (total < INT_MAX)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  (CharArray.undef_full retval total )
  **  ((( &( "strings_size" ) )) # Int  |-> strings_size_pre)
  **  ((( &( "strings" ) )) # Ptr  |-> strings_pre)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "len0" ) )) # Int  |-> len0)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  (CharPtrArray2.full strings_pre strings_size_pre rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition concatenate_safety_wit_11 := 
forall (strings_size_pre: Z) (strings_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (out_l: (@list Z)) (i: Z) (len: Z) (k: Z) (total: Z) (len0: Z) (out: Z) (retval: Z) (PreH1 : (retval = (out + (k * sizeof(CHAR) ) ))) (PreH2 : (0 <= k)) (PreH3 : (0 <= i)) (PreH4 : (i < strings_size_pre)) (PreH5 : (0 <= strings_size_pre)) (PreH6 : (strings_size_pre <= 100)) (PreH7 : (len = (row_len_z_28 ((Znth (i) (rows) ((@nil Z))))))) (PreH8 : ((k + len ) < total)) (PreH9 : (0 <= len0)) (PreH10 : (len0 < INT_MAX)) (PreH11 : (0 <= len)) (PreH12 : (len < INT_MAX)) (PreH13 : (rows_well_formed_28 rows strings_size_pre )) (PreH14 : forall (p: Z) , (((0 <= p) /\ (p <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p)) + 1 ) < INT_MAX))) (PreH15 : (problem_28_pre_z rows )) (PreH16 : (total_prefix_state_28 rows strings_size_pre total )) (PreH17 : (copy_prefix_state_28 rows i k out_l )) (PreH18 : (all_ascii (row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))) )) (PreH19 : ((Zlength ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) = len)) ,
  (CharArray.full (out + (k * sizeof(CHAR) ) ) len (row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))) )
  **  (CharArray.full row_ptr len (row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "strings_size" ) )) # Int  |-> strings_size_pre)
  **  ((( &( "strings" ) )) # Ptr  |-> strings_pre)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "len0" ) )) # Int  |-> len0)
  **  (CharPtrArray2.missing_i strings_pre strings_size_pre i row_ptr rows )
  **  (((strings_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.seg row_ptr len (len + 1 ) (cons (0) ((@nil Z))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out k out_l )
  **  (CharArray.undef_seg out (k + len ) total )
|--
  “ ((k + len ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + len )) ”
.

Definition concatenate_safety_wit_12 := 
forall (strings_size_pre: Z) (strings_pre: Z) (rows: (@list (@list Z))) (out_l: (@list Z)) (i: Z) (cur: Z) (len0: Z) (len: Z) (total: Z) (k: Z) (out: Z) (PreH1 : (0 <= i)) (PreH2 : (i < strings_size_pre)) (PreH3 : (0 <= strings_size_pre)) (PreH4 : (strings_size_pre <= 100)) (PreH5 : (0 <= len0)) (PreH6 : (len0 < INT_MAX)) (PreH7 : (0 <= len)) (PreH8 : (len < INT_MAX)) (PreH9 : (rows_well_formed_28 rows strings_size_pre )) (PreH10 : forall (p: Z) , (((0 <= p) /\ (p <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p)) + 1 ) < INT_MAX))) (PreH11 : (problem_28_pre_z rows )) (PreH12 : (total_prefix_state_28 rows strings_size_pre total )) (PreH13 : (copy_prefix_state_28 rows (i + 1 ) k out_l )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "strings_size" ) )) # Int  |-> strings_size_pre)
  **  ((( &( "strings" ) )) # Ptr  |-> strings_pre)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "len0" ) )) # Int  |-> len0)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (CharPtrArray2.full strings_pre strings_size_pre rows )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out k out_l )
  **  (CharArray.undef_seg out k total )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition concatenate_safety_wit_13 := 
forall (strings_size_pre: Z) (strings_pre: Z) (rows: (@list (@list Z))) (out_l: (@list Z)) (k: Z) (total: Z) (cur: Z) (len0: Z) (len: Z) (out: Z) (PreH1 : ((k + 1 ) = total)) (PreH2 : (rows_well_formed_28 rows strings_size_pre )) (PreH3 : forall (p: Z) , (((0 <= p) /\ (p <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p)) + 1 ) < INT_MAX))) (PreH4 : (0 <= len0)) (PreH5 : (len0 < INT_MAX)) (PreH6 : (0 <= len)) (PreH7 : (len < INT_MAX)) (PreH8 : (problem_28_pre_z rows )) (PreH9 : (copy_prefix_state_28 rows strings_size_pre k out_l )) ,
  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "strings_size" ) )) # Int  |-> strings_size_pre)
  **  ((( &( "strings" ) )) # Ptr  |-> strings_pre)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "len0" ) )) # Int  |-> len0)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  (CharPtrArray2.full strings_pre strings_size_pre rows )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out k out_l )
  **  (CharArray.undef_seg out k (k + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition concatenate_entail_wit_1 := 
(
forall (strings_size_pre: Z) (strings_pre: Z) (rows: (@list (@list Z))) (PreH1 : (0 <= strings_size_pre)) (PreH2 : (strings_size_pre <= 100)) (PreH3 : (rows_well_formed_28 rows strings_size_pre )) (PreH4 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p_2)) + 1 ) < INT_MAX))) (PreH5 : (problem_28_pre_z rows )) ,
  (CharPtrArray2.full strings_pre strings_size_pre rows )
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= strings_size_pre) ” 
  &&  “ (0 <= strings_size_pre) ” 
  &&  “ (strings_size_pre <= 100) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 < INT_MAX) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 < INT_MAX) ” 
  &&  “ (rows_well_formed_28 rows strings_size_pre ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p)) + 1 ) < INT_MAX)) ” 
  &&  “ (problem_28_pre_z rows ) ” 
  &&  “ (total_prefix_state_28 rows 0 1 ) ” 
  &&  “ (0 < 1) ” 
  &&  “ (1 < INT_MAX) ”
  &&  (CharPtrArray2.full strings_pre strings_size_pre rows )
) \/
(
forall (strings_size_pre: Z) (rows: (@list (@list Z))) (PreH1 : (0 <= strings_size_pre)) (PreH2 : (strings_size_pre <= 100)) (PreH3 : (rows_well_formed_28 rows strings_size_pre )) (PreH4 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p_2)) + 1 ) < INT_MAX))) (PreH5 : (problem_28_pre_z rows )) ,
  TT && emp 
|--
  “ (total_prefix_state_28 rows 0 1 ) ”
  &&  emp
).

Definition concatenate_entail_wit_1_split_goal_1 := 
forall (strings_size_pre: Z) (rows: (@list (@list Z))) (PreH1 : (0 <= strings_size_pre)) (PreH2 : (strings_size_pre <= 100)) (PreH3 : (rows_well_formed_28 rows strings_size_pre )) (PreH4 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p_2)) + 1 ) < INT_MAX))) (PreH5 : (problem_28_pre_z rows )) ,
  TT && emp 
|--
  “ (total_prefix_state_28 rows 0 1 ) ”
.

Definition concatenate_entail_wit_2 := 
(
forall (strings_size_pre: Z) (strings_pre: Z) (rows: (@list (@list Z))) (total: Z) (len: Z) (len0: Z) (k: Z) (out: Z) (i: Z) (PreH1 : (i < strings_size_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= strings_size_pre)) (PreH4 : (0 <= strings_size_pre)) (PreH5 : (strings_size_pre <= 100)) (PreH6 : (out = 0)) (PreH7 : (k = 0)) (PreH8 : (0 <= len0)) (PreH9 : (len0 < INT_MAX)) (PreH10 : (0 <= len)) (PreH11 : (len < INT_MAX)) (PreH12 : (rows_well_formed_28 rows strings_size_pre )) (PreH13 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p_2)) + 1 ) < INT_MAX))) (PreH14 : (problem_28_pre_z rows )) (PreH15 : (total_prefix_state_28 rows i total )) (PreH16 : (0 < total)) (PreH17 : (total < INT_MAX)) ,
  (CharPtrArray2.full strings_pre strings_size_pre rows )
|--
  EX (row_ptr: Z) ,
  “ (0 <= i) ” 
  &&  “ (i < strings_size_pre) ” 
  &&  “ (0 <= strings_size_pre) ” 
  &&  “ (strings_size_pre <= 100) ” 
  &&  “ (out = 0) ” 
  &&  “ (k = 0) ” 
  &&  “ (0 <= len0) ” 
  &&  “ (len0 < INT_MAX) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (rows_well_formed_28 rows strings_size_pre ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p)) + 1 ) < INT_MAX)) ” 
  &&  “ (problem_28_pre_z rows ) ” 
  &&  “ (total_prefix_state_28 rows i total ) ” 
  &&  “ (valid_string (row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))) ) ” 
  &&  “ ((string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX) ” 
  &&  “ ((Zlength ((Znth (i) (rows) ((@nil Z))))) = ((string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) + 1 )) ”
  &&  (CharPtrArray2.missing_i strings_pre strings_size_pre i row_ptr rows )
  **  (((strings_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))) )
) \/
(
forall (strings_size_pre: Z) (rows: (@list (@list Z))) (total: Z) (len: Z) (len0: Z) (k: Z) (out: Z) (i: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (0 <= (Zlength ((Znth i rows __default__List_Z))))) (PreH2 : (i < strings_size_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= strings_size_pre)) (PreH5 : (0 <= strings_size_pre)) (PreH6 : (strings_size_pre <= 100)) (PreH7 : (out = 0)) (PreH8 : (k = 0)) (PreH9 : (0 <= len0)) (PreH10 : (len0 < INT_MAX)) (PreH11 : (0 <= len)) (PreH12 : (len < INT_MAX)) (PreH13 : (rows_well_formed_28 rows strings_size_pre )) (PreH14 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p_2)) + 1 ) < INT_MAX))) (PreH15 : (problem_28_pre_z rows )) (PreH16 : (total_prefix_state_28 rows i total )) (PreH17 : (0 < total)) (PreH18 : (total < INT_MAX)) ,
  (CharArray.full row_ptr_2 (Zlength ((Znth i rows __default__List_Z))) (Znth i rows __default__List_Z) )
|--
  “ ((Zlength ((Znth (i) (rows) ((@nil Z))))) = ((string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) + 1 )) ” 
  &&  “ ((string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX) ” 
  &&  “ (valid_string (row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))) ) ”
  &&  (CharArray.full row_ptr_2 ((string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) )
).

Definition concatenate_entail_wit_2_split_goal_1 := 
forall (strings_size_pre: Z) (rows: (@list (@list Z))) (total: Z) (len: Z) (len0: Z) (k: Z) (out: Z) (i: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (0 <= (Zlength ((Znth i rows __default__List_Z))))) (PreH2 : (i < strings_size_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= strings_size_pre)) (PreH5 : (0 <= strings_size_pre)) (PreH6 : (strings_size_pre <= 100)) (PreH7 : (out = 0)) (PreH8 : (k = 0)) (PreH9 : (0 <= len0)) (PreH10 : (len0 < INT_MAX)) (PreH11 : (0 <= len)) (PreH12 : (len < INT_MAX)) (PreH13 : (rows_well_formed_28 rows strings_size_pre )) (PreH14 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p_2)) + 1 ) < INT_MAX))) (PreH15 : (problem_28_pre_z rows )) (PreH16 : (total_prefix_state_28 rows i total )) (PreH17 : (0 < total)) (PreH18 : (total < INT_MAX)) ,
  (CharArray.full row_ptr_2 (Zlength ((Znth i rows __default__List_Z))) (Znth i rows __default__List_Z) )
|--
  “ ((Zlength ((Znth (i) (rows) ((@nil Z))))) = ((string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) + 1 )) ”
.

Definition concatenate_entail_wit_2_split_goal_2 := 
forall (strings_size_pre: Z) (rows: (@list (@list Z))) (total: Z) (len: Z) (len0: Z) (k: Z) (out: Z) (i: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (0 <= (Zlength ((Znth i rows __default__List_Z))))) (PreH2 : (i < strings_size_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= strings_size_pre)) (PreH5 : (0 <= strings_size_pre)) (PreH6 : (strings_size_pre <= 100)) (PreH7 : (out = 0)) (PreH8 : (k = 0)) (PreH9 : (0 <= len0)) (PreH10 : (len0 < INT_MAX)) (PreH11 : (0 <= len)) (PreH12 : (len < INT_MAX)) (PreH13 : (rows_well_formed_28 rows strings_size_pre )) (PreH14 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p_2)) + 1 ) < INT_MAX))) (PreH15 : (problem_28_pre_z rows )) (PreH16 : (total_prefix_state_28 rows i total )) (PreH17 : (0 < total)) (PreH18 : (total < INT_MAX)) ,
  (CharArray.full row_ptr_2 (Zlength ((Znth i rows __default__List_Z))) (Znth i rows __default__List_Z) )
|--
  “ ((string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX) ”
.

Definition concatenate_entail_wit_2_split_goal_3 := 
forall (strings_size_pre: Z) (rows: (@list (@list Z))) (total: Z) (len: Z) (len0: Z) (k: Z) (out: Z) (i: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (0 <= (Zlength ((Znth i rows __default__List_Z))))) (PreH2 : (i < strings_size_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= strings_size_pre)) (PreH5 : (0 <= strings_size_pre)) (PreH6 : (strings_size_pre <= 100)) (PreH7 : (out = 0)) (PreH8 : (k = 0)) (PreH9 : (0 <= len0)) (PreH10 : (len0 < INT_MAX)) (PreH11 : (0 <= len)) (PreH12 : (len < INT_MAX)) (PreH13 : (rows_well_formed_28 rows strings_size_pre )) (PreH14 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p_2)) + 1 ) < INT_MAX))) (PreH15 : (problem_28_pre_z rows )) (PreH16 : (total_prefix_state_28 rows i total )) (PreH17 : (0 < total)) (PreH18 : (total < INT_MAX)) ,
  (CharArray.full row_ptr_2 (Zlength ((Znth i rows __default__List_Z))) (Znth i rows __default__List_Z) )
|--
  “ (valid_string (row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))) ) ”
.

Definition concatenate_entail_wit_2_split_goal_spatial := 
forall (strings_size_pre: Z) (rows: (@list (@list Z))) (total: Z) (len: Z) (len0: Z) (k: Z) (out: Z) (i: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (0 <= (Zlength ((Znth i rows __default__List_Z))))) (PreH2 : (i < strings_size_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= strings_size_pre)) (PreH5 : (0 <= strings_size_pre)) (PreH6 : (strings_size_pre <= 100)) (PreH7 : (out = 0)) (PreH8 : (k = 0)) (PreH9 : (0 <= len0)) (PreH10 : (len0 < INT_MAX)) (PreH11 : (0 <= len)) (PreH12 : (len < INT_MAX)) (PreH13 : (rows_well_formed_28 rows strings_size_pre )) (PreH14 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p_2)) + 1 ) < INT_MAX))) (PreH15 : (problem_28_pre_z rows )) (PreH16 : (total_prefix_state_28 rows i total )) (PreH17 : (0 < total)) (PreH18 : (total < INT_MAX)) ,
  (CharArray.full row_ptr_2 (Zlength ((Znth i rows __default__List_Z))) (Znth i rows __default__List_Z) )
|--
  (CharArray.full row_ptr_2 ((string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) )
.

Definition concatenate_entail_wit_3 := 
forall (strings_size_pre: Z) (strings_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (i: Z) (out: Z) (k: Z) (len0: Z) (len: Z) (total: Z) (PreH1 : (0 <= i)) (PreH2 : (i < strings_size_pre)) (PreH3 : (0 <= strings_size_pre)) (PreH4 : (strings_size_pre <= 100)) (PreH5 : (out = 0)) (PreH6 : (k = 0)) (PreH7 : (0 <= len0)) (PreH8 : (len0 < INT_MAX)) (PreH9 : (0 <= len)) (PreH10 : (len < INT_MAX)) (PreH11 : (rows_well_formed_28 rows strings_size_pre )) (PreH12 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p_2)) + 1 ) < INT_MAX))) (PreH13 : (problem_28_pre_z rows )) (PreH14 : (total_prefix_state_28 rows i total )) (PreH15 : (valid_string (row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))) )) (PreH16 : ((string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX)) (PreH17 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = ((string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) ,
  (CharPtrArray2.missing_i strings_pre strings_size_pre i row_ptr rows )
  **  (((strings_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))) )
|--
  “ (0 <= i) ” 
  &&  “ (i < strings_size_pre) ” 
  &&  “ (0 <= strings_size_pre) ” 
  &&  “ (strings_size_pre <= 100) ” 
  &&  “ (out = 0) ” 
  &&  “ (k = 0) ” 
  &&  “ (0 <= len0) ” 
  &&  “ (len0 < INT_MAX) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (rows_well_formed_28 rows strings_size_pre ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p)) + 1 ) < INT_MAX)) ” 
  &&  “ (problem_28_pre_z rows ) ” 
  &&  “ (total_prefix_state_28 rows i total ) ” 
  &&  “ (valid_string (row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))) ) ” 
  &&  “ ((string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX) ” 
  &&  “ ((Zlength ((Znth (i) (rows) ((@nil Z))))) = ((string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) + 1 )) ”
  &&  (CharPtrArray2.missing_i strings_pre strings_size_pre i row_ptr rows )
  **  (((strings_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))) )
.

Definition concatenate_entail_wit_4 := 
(
forall (strings_size_pre: Z) (strings_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (i: Z) (out: Z) (k: Z) (len0: Z) (len: Z) (total: Z) (retval: Z) (PreH1 : (retval = (string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))))) (PreH2 : (0 <= ((string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < strings_size_pre)) (PreH5 : (0 <= strings_size_pre)) (PreH6 : (strings_size_pre <= 100)) (PreH7 : (out = 0)) (PreH8 : (k = 0)) (PreH9 : (0 <= len0)) (PreH10 : (len0 < INT_MAX)) (PreH11 : (0 <= len)) (PreH12 : (len < INT_MAX)) (PreH13 : (rows_well_formed_28 rows strings_size_pre )) (PreH14 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p_2)) + 1 ) < INT_MAX))) (PreH15 : (problem_28_pre_z rows )) (PreH16 : (total_prefix_state_28 rows i total )) (PreH17 : (valid_string (row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))) )) (PreH18 : ((string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX)) (PreH19 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = ((string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) ,
  (store_string row_ptr (row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))) )
  **  (CharPtrArray2.missing_i strings_pre strings_size_pre i row_ptr rows )
  **  (((strings_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ (0 <= i) ” 
  &&  “ (i < strings_size_pre) ” 
  &&  “ (0 <= strings_size_pre) ” 
  &&  “ (strings_size_pre <= 100) ” 
  &&  “ (out = 0) ” 
  &&  “ (k = 0) ” 
  &&  “ (retval = (row_len_z_28 ((Znth (i) (rows) ((@nil Z)))))) ” 
  &&  “ ((total + retval ) < INT_MAX) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < INT_MAX) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (rows_well_formed_28 rows strings_size_pre ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p)) + 1 ) < INT_MAX)) ” 
  &&  “ (problem_28_pre_z rows ) ” 
  &&  “ (total_prefix_state_28 rows i total ) ”
  &&  (CharPtrArray2.missing_i strings_pre strings_size_pre i row_ptr rows )
  **  (((strings_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
) \/
(
forall (strings_size_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (i: Z) (out: Z) (k: Z) (len0: Z) (len: Z) (total: Z) (retval: Z) (PreH1 : (retval = (string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))))) (PreH2 : (0 <= ((string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < strings_size_pre)) (PreH5 : (0 <= strings_size_pre)) (PreH6 : (strings_size_pre <= 100)) (PreH7 : (out = 0)) (PreH8 : (k = 0)) (PreH9 : (0 <= len0)) (PreH10 : (len0 < INT_MAX)) (PreH11 : (0 <= len)) (PreH12 : (len < INT_MAX)) (PreH13 : (rows_well_formed_28 rows strings_size_pre )) (PreH14 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p_2)) + 1 ) < INT_MAX))) (PreH15 : (problem_28_pre_z rows )) (PreH16 : (total_prefix_state_28 rows i total )) (PreH17 : (valid_string (row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))) )) (PreH18 : ((string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX)) (PreH19 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = ((string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) ,
  (CharArray.full row_ptr ((string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) )
|--
  “ (0 <= retval) ” 
  &&  “ ((total + retval ) < INT_MAX) ” 
  &&  “ (retval = (row_len_z_28 ((Znth (i) (rows) ((@nil Z)))))) ”
  &&  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
).

Definition concatenate_entail_wit_4_split_goal_1 := 
forall (strings_size_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (i: Z) (out: Z) (k: Z) (len0: Z) (len: Z) (total: Z) (retval: Z) (PreH1 : (retval = (string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))))) (PreH2 : (0 <= ((string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < strings_size_pre)) (PreH5 : (0 <= strings_size_pre)) (PreH6 : (strings_size_pre <= 100)) (PreH7 : (out = 0)) (PreH8 : (k = 0)) (PreH9 : (0 <= len0)) (PreH10 : (len0 < INT_MAX)) (PreH11 : (0 <= len)) (PreH12 : (len < INT_MAX)) (PreH13 : (rows_well_formed_28 rows strings_size_pre )) (PreH14 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p_2)) + 1 ) < INT_MAX))) (PreH15 : (problem_28_pre_z rows )) (PreH16 : (total_prefix_state_28 rows i total )) (PreH17 : (valid_string (row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))) )) (PreH18 : ((string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX)) (PreH19 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = ((string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) ,
  (CharArray.full row_ptr ((string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) )
|--
  “ (0 <= retval) ”
.

Definition concatenate_entail_wit_4_split_goal_2 := 
forall (strings_size_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (i: Z) (out: Z) (k: Z) (len0: Z) (len: Z) (total: Z) (retval: Z) (PreH1 : (retval = (string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))))) (PreH2 : (0 <= ((string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < strings_size_pre)) (PreH5 : (0 <= strings_size_pre)) (PreH6 : (strings_size_pre <= 100)) (PreH7 : (out = 0)) (PreH8 : (k = 0)) (PreH9 : (0 <= len0)) (PreH10 : (len0 < INT_MAX)) (PreH11 : (0 <= len)) (PreH12 : (len < INT_MAX)) (PreH13 : (rows_well_formed_28 rows strings_size_pre )) (PreH14 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p_2)) + 1 ) < INT_MAX))) (PreH15 : (problem_28_pre_z rows )) (PreH16 : (total_prefix_state_28 rows i total )) (PreH17 : (valid_string (row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))) )) (PreH18 : ((string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX)) (PreH19 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = ((string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) ,
  (CharArray.full row_ptr ((string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) )
|--
  “ ((total + retval ) < INT_MAX) ”
.

Definition concatenate_entail_wit_4_split_goal_3 := 
forall (strings_size_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (i: Z) (out: Z) (k: Z) (len0: Z) (len: Z) (total: Z) (retval: Z) (PreH1 : (retval = (string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))))) (PreH2 : (0 <= ((string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < strings_size_pre)) (PreH5 : (0 <= strings_size_pre)) (PreH6 : (strings_size_pre <= 100)) (PreH7 : (out = 0)) (PreH8 : (k = 0)) (PreH9 : (0 <= len0)) (PreH10 : (len0 < INT_MAX)) (PreH11 : (0 <= len)) (PreH12 : (len < INT_MAX)) (PreH13 : (rows_well_formed_28 rows strings_size_pre )) (PreH14 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p_2)) + 1 ) < INT_MAX))) (PreH15 : (problem_28_pre_z rows )) (PreH16 : (total_prefix_state_28 rows i total )) (PreH17 : (valid_string (row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))) )) (PreH18 : ((string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX)) (PreH19 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = ((string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) ,
  (CharArray.full row_ptr ((string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) )
|--
  “ (retval = (row_len_z_28 ((Znth (i) (rows) ((@nil Z)))))) ”
.

Definition concatenate_entail_wit_4_split_goal_spatial := 
forall (strings_size_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (i: Z) (out: Z) (k: Z) (len0: Z) (len: Z) (total: Z) (retval: Z) (PreH1 : (retval = (string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))))) (PreH2 : (0 <= ((string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < strings_size_pre)) (PreH5 : (0 <= strings_size_pre)) (PreH6 : (strings_size_pre <= 100)) (PreH7 : (out = 0)) (PreH8 : (k = 0)) (PreH9 : (0 <= len0)) (PreH10 : (len0 < INT_MAX)) (PreH11 : (0 <= len)) (PreH12 : (len < INT_MAX)) (PreH13 : (rows_well_formed_28 rows strings_size_pre )) (PreH14 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p_2)) + 1 ) < INT_MAX))) (PreH15 : (problem_28_pre_z rows )) (PreH16 : (total_prefix_state_28 rows i total )) (PreH17 : (valid_string (row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))) )) (PreH18 : ((string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX)) (PreH19 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = ((string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) ,
  (CharArray.full row_ptr ((string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) )
|--
  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
.

Definition concatenate_entail_wit_5 := 
(
forall (strings_size_pre: Z) (strings_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (i: Z) (out: Z) (k: Z) (len0: Z) (total: Z) (len: Z) (PreH1 : (0 <= i)) (PreH2 : (i < strings_size_pre)) (PreH3 : (0 <= strings_size_pre)) (PreH4 : (strings_size_pre <= 100)) (PreH5 : (out = 0)) (PreH6 : (k = 0)) (PreH7 : (len0 = (row_len_z_28 ((Znth (i) (rows) ((@nil Z))))))) (PreH8 : ((total + len0 ) < INT_MAX)) (PreH9 : (0 <= len0)) (PreH10 : (len0 < INT_MAX)) (PreH11 : (0 <= len)) (PreH12 : (len < INT_MAX)) (PreH13 : (rows_well_formed_28 rows strings_size_pre )) (PreH14 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p_2)) + 1 ) < INT_MAX))) (PreH15 : (problem_28_pre_z rows )) (PreH16 : (total_prefix_state_28 rows i total )) ,
  (CharPtrArray2.missing_i strings_pre strings_size_pre i row_ptr rows )
  **  (((strings_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
|--
  “ (0 <= i) ” 
  &&  “ (i < strings_size_pre) ” 
  &&  “ (0 <= strings_size_pre) ” 
  &&  “ (strings_size_pre <= 100) ” 
  &&  “ (out = 0) ” 
  &&  “ (k = 0) ” 
  &&  “ (len0 = (row_len_z_28 ((Znth (i) (rows) ((@nil Z)))))) ” 
  &&  “ (0 <= len0) ” 
  &&  “ (len0 < INT_MAX) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (rows_well_formed_28 rows strings_size_pre ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p)) + 1 ) < INT_MAX)) ” 
  &&  “ (problem_28_pre_z rows ) ” 
  &&  “ (total_prefix_state_28 rows (i + 1 ) (total + len0 ) ) ” 
  &&  “ (0 < (total + len0 )) ” 
  &&  “ ((total + len0 ) < INT_MAX) ”
  &&  (CharPtrArray2.full strings_pre strings_size_pre rows )
) \/
(
forall (strings_size_pre: Z) (strings_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (i: Z) (out: Z) (k: Z) (len0: Z) (total: Z) (len: Z) (PreH1 : (0 <= (Zlength ((Znth (i) (rows) ((@nil Z))))))) (PreH2 : (0 <= i)) (PreH3 : (i < strings_size_pre)) (PreH4 : (0 <= strings_size_pre)) (PreH5 : (strings_size_pre <= 100)) (PreH6 : (out = 0)) (PreH7 : (k = 0)) (PreH8 : (len0 = (row_len_z_28 ((Znth (i) (rows) ((@nil Z))))))) (PreH9 : ((total + len0 ) < INT_MAX)) (PreH10 : (0 <= len0)) (PreH11 : (len0 < INT_MAX)) (PreH12 : (0 <= len)) (PreH13 : (len < INT_MAX)) (PreH14 : (rows_well_formed_28 rows strings_size_pre )) (PreH15 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p_2)) + 1 ) < INT_MAX))) (PreH16 : (problem_28_pre_z rows )) (PreH17 : (total_prefix_state_28 rows i total )) ,
  (CharPtrArray2.missing_i strings_pre strings_size_pre i row_ptr rows )
  **  (((strings_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
|--
  “ (0 < (total + len0 )) ” 
  &&  “ (total_prefix_state_28 rows (i + 1 ) (total + len0 ) ) ”
  &&  (CharPtrArray2.full strings_pre strings_size_pre rows )
).

Definition concatenate_entail_wit_5_split_goal_1 := 
forall (strings_size_pre: Z) (strings_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (i: Z) (out: Z) (k: Z) (len0: Z) (total: Z) (len: Z) (PreH1 : (0 <= (Zlength ((Znth (i) (rows) ((@nil Z))))))) (PreH2 : (0 <= i)) (PreH3 : (i < strings_size_pre)) (PreH4 : (0 <= strings_size_pre)) (PreH5 : (strings_size_pre <= 100)) (PreH6 : (out = 0)) (PreH7 : (k = 0)) (PreH8 : (len0 = (row_len_z_28 ((Znth (i) (rows) ((@nil Z))))))) (PreH9 : ((total + len0 ) < INT_MAX)) (PreH10 : (0 <= len0)) (PreH11 : (len0 < INT_MAX)) (PreH12 : (0 <= len)) (PreH13 : (len < INT_MAX)) (PreH14 : (rows_well_formed_28 rows strings_size_pre )) (PreH15 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p_2)) + 1 ) < INT_MAX))) (PreH16 : (problem_28_pre_z rows )) (PreH17 : (total_prefix_state_28 rows i total )) ,
  (CharPtrArray2.missing_i strings_pre strings_size_pre i row_ptr rows )
  **  (((strings_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
|--
  “ (0 < (total + len0 )) ”
.

Definition concatenate_entail_wit_5_split_goal_2 := 
forall (strings_size_pre: Z) (strings_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (i: Z) (out: Z) (k: Z) (len0: Z) (total: Z) (len: Z) (PreH1 : (0 <= (Zlength ((Znth (i) (rows) ((@nil Z))))))) (PreH2 : (0 <= i)) (PreH3 : (i < strings_size_pre)) (PreH4 : (0 <= strings_size_pre)) (PreH5 : (strings_size_pre <= 100)) (PreH6 : (out = 0)) (PreH7 : (k = 0)) (PreH8 : (len0 = (row_len_z_28 ((Znth (i) (rows) ((@nil Z))))))) (PreH9 : ((total + len0 ) < INT_MAX)) (PreH10 : (0 <= len0)) (PreH11 : (len0 < INT_MAX)) (PreH12 : (0 <= len)) (PreH13 : (len < INT_MAX)) (PreH14 : (rows_well_formed_28 rows strings_size_pre )) (PreH15 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p_2)) + 1 ) < INT_MAX))) (PreH16 : (problem_28_pre_z rows )) (PreH17 : (total_prefix_state_28 rows i total )) ,
  (CharPtrArray2.missing_i strings_pre strings_size_pre i row_ptr rows )
  **  (((strings_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
|--
  “ (total_prefix_state_28 rows (i + 1 ) (total + len0 ) ) ”
.

Definition concatenate_entail_wit_5_split_goal_spatial := 
forall (strings_size_pre: Z) (strings_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (i: Z) (out: Z) (k: Z) (len0: Z) (total: Z) (len: Z) (PreH1 : (0 <= (Zlength ((Znth (i) (rows) ((@nil Z))))))) (PreH2 : (0 <= i)) (PreH3 : (i < strings_size_pre)) (PreH4 : (0 <= strings_size_pre)) (PreH5 : (strings_size_pre <= 100)) (PreH6 : (out = 0)) (PreH7 : (k = 0)) (PreH8 : (len0 = (row_len_z_28 ((Znth (i) (rows) ((@nil Z))))))) (PreH9 : ((total + len0 ) < INT_MAX)) (PreH10 : (0 <= len0)) (PreH11 : (len0 < INT_MAX)) (PreH12 : (0 <= len)) (PreH13 : (len < INT_MAX)) (PreH14 : (rows_well_formed_28 rows strings_size_pre )) (PreH15 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p_2)) + 1 ) < INT_MAX))) (PreH16 : (problem_28_pre_z rows )) (PreH17 : (total_prefix_state_28 rows i total )) ,
  (CharPtrArray2.missing_i strings_pre strings_size_pre i row_ptr rows )
  **  (((strings_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
|--
  (CharPtrArray2.full strings_pre strings_size_pre rows )
.

Definition concatenate_entail_wit_6 := 
forall (strings_size_pre: Z) (strings_pre: Z) (rows: (@list (@list Z))) (i: Z) (out: Z) (k: Z) (len0: Z) (len: Z) (total: Z) (PreH1 : (0 <= i)) (PreH2 : (i < strings_size_pre)) (PreH3 : (0 <= strings_size_pre)) (PreH4 : (strings_size_pre <= 100)) (PreH5 : (out = 0)) (PreH6 : (k = 0)) (PreH7 : (len0 = (row_len_z_28 ((Znth (i) (rows) ((@nil Z))))))) (PreH8 : (0 <= len0)) (PreH9 : (len0 < INT_MAX)) (PreH10 : (0 <= len)) (PreH11 : (len < INT_MAX)) (PreH12 : (rows_well_formed_28 rows strings_size_pre )) (PreH13 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p_2)) + 1 ) < INT_MAX))) (PreH14 : (problem_28_pre_z rows )) (PreH15 : (total_prefix_state_28 rows (i + 1 ) total )) (PreH16 : (0 < total)) (PreH17 : (total < INT_MAX)) ,
  (CharPtrArray2.full strings_pre strings_size_pre rows )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= strings_size_pre) ” 
  &&  “ (0 <= strings_size_pre) ” 
  &&  “ (strings_size_pre <= 100) ” 
  &&  “ (out = 0) ” 
  &&  “ (k = 0) ” 
  &&  “ (0 <= len0) ” 
  &&  “ (len0 < INT_MAX) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (rows_well_formed_28 rows strings_size_pre ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p)) + 1 ) < INT_MAX)) ” 
  &&  “ (problem_28_pre_z rows ) ” 
  &&  “ (total_prefix_state_28 rows (i + 1 ) total ) ” 
  &&  “ (0 < total) ” 
  &&  “ (total < INT_MAX) ”
  &&  (CharPtrArray2.full strings_pre strings_size_pre rows )
.

Definition concatenate_entail_wit_7 := 
(
forall (strings_size_pre: Z) (strings_pre: Z) (rows: (@list (@list Z))) (total: Z) (len: Z) (len0: Z) (k: Z) (out: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (i >= strings_size_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= strings_size_pre)) (PreH5 : (0 <= strings_size_pre)) (PreH6 : (strings_size_pre <= 100)) (PreH7 : (out = 0)) (PreH8 : (k = 0)) (PreH9 : (0 <= len0)) (PreH10 : (len0 < INT_MAX)) (PreH11 : (0 <= len)) (PreH12 : (len < INT_MAX)) (PreH13 : (rows_well_formed_28 rows strings_size_pre )) (PreH14 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p_2)) + 1 ) < INT_MAX))) (PreH15 : (problem_28_pre_z rows )) (PreH16 : (total_prefix_state_28 rows i total )) (PreH17 : (0 < total)) (PreH18 : (total < INT_MAX)) ,
  (CharArray.undef_full retval total )
  **  (CharPtrArray2.full strings_pre strings_size_pre rows )
|--
  EX (out_l: (@list Z)) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= strings_size_pre) ” 
  &&  “ (0 <= strings_size_pre) ” 
  &&  “ (strings_size_pre <= 100) ” 
  &&  “ (0 <= len0) ” 
  &&  “ (len0 < INT_MAX) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (rows_well_formed_28 rows strings_size_pre ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p)) + 1 ) < INT_MAX)) ” 
  &&  “ (problem_28_pre_z rows ) ” 
  &&  “ (total_prefix_state_28 rows strings_size_pre total ) ” 
  &&  “ (copy_prefix_state_28 rows 0 k out_l ) ”
  &&  (CharPtrArray2.full strings_pre strings_size_pre rows )
  **  (CharArray.full retval k out_l )
  **  (CharArray.undef_seg retval k total )
) \/
(
forall (strings_size_pre: Z) (rows: (@list (@list Z))) (total: Z) (len: Z) (len0: Z) (k: Z) (out: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (i >= strings_size_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= strings_size_pre)) (PreH5 : (0 <= strings_size_pre)) (PreH6 : (strings_size_pre <= 100)) (PreH7 : (out = 0)) (PreH8 : (k = 0)) (PreH9 : (0 <= len0)) (PreH10 : (len0 < INT_MAX)) (PreH11 : (0 <= len)) (PreH12 : (len < INT_MAX)) (PreH13 : (rows_well_formed_28 rows strings_size_pre )) (PreH14 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p_2)) + 1 ) < INT_MAX))) (PreH15 : (problem_28_pre_z rows )) (PreH16 : (total_prefix_state_28 rows i total )) (PreH17 : (0 < total)) (PreH18 : (total < INT_MAX)) ,
  (CharArray.undef_full retval total )
|--
  “ (copy_prefix_state_28 rows 0 k (@nil Z) ) ” 
  &&  “ (total_prefix_state_28 rows strings_size_pre total ) ”
  &&  (CharArray.undef_full retval total )
).

Definition concatenate_entail_wit_7_split_goal_1 := 
forall (strings_size_pre: Z) (rows: (@list (@list Z))) (total: Z) (len: Z) (len0: Z) (k: Z) (out: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (i >= strings_size_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= strings_size_pre)) (PreH5 : (0 <= strings_size_pre)) (PreH6 : (strings_size_pre <= 100)) (PreH7 : (out = 0)) (PreH8 : (k = 0)) (PreH9 : (0 <= len0)) (PreH10 : (len0 < INT_MAX)) (PreH11 : (0 <= len)) (PreH12 : (len < INT_MAX)) (PreH13 : (rows_well_formed_28 rows strings_size_pre )) (PreH14 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p_2)) + 1 ) < INT_MAX))) (PreH15 : (problem_28_pre_z rows )) (PreH16 : (total_prefix_state_28 rows i total )) (PreH17 : (0 < total)) (PreH18 : (total < INT_MAX)) ,
  (CharArray.undef_full retval total )
|--
  “ (copy_prefix_state_28 rows 0 k (@nil Z) ) ”
.

Definition concatenate_entail_wit_7_split_goal_2 := 
forall (strings_size_pre: Z) (rows: (@list (@list Z))) (total: Z) (len: Z) (len0: Z) (k: Z) (out: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (i >= strings_size_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= strings_size_pre)) (PreH5 : (0 <= strings_size_pre)) (PreH6 : (strings_size_pre <= 100)) (PreH7 : (out = 0)) (PreH8 : (k = 0)) (PreH9 : (0 <= len0)) (PreH10 : (len0 < INT_MAX)) (PreH11 : (0 <= len)) (PreH12 : (len < INT_MAX)) (PreH13 : (rows_well_formed_28 rows strings_size_pre )) (PreH14 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p_2)) + 1 ) < INT_MAX))) (PreH15 : (problem_28_pre_z rows )) (PreH16 : (total_prefix_state_28 rows i total )) (PreH17 : (0 < total)) (PreH18 : (total < INT_MAX)) ,
  (CharArray.undef_full retval total )
|--
  “ (total_prefix_state_28 rows strings_size_pre total ) ”
.

Definition concatenate_entail_wit_7_split_goal_spatial := 
forall (strings_size_pre: Z) (rows: (@list (@list Z))) (total: Z) (len: Z) (len0: Z) (k: Z) (out: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (i >= strings_size_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= strings_size_pre)) (PreH5 : (0 <= strings_size_pre)) (PreH6 : (strings_size_pre <= 100)) (PreH7 : (out = 0)) (PreH8 : (k = 0)) (PreH9 : (0 <= len0)) (PreH10 : (len0 < INT_MAX)) (PreH11 : (0 <= len)) (PreH12 : (len < INT_MAX)) (PreH13 : (rows_well_formed_28 rows strings_size_pre )) (PreH14 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p_2)) + 1 ) < INT_MAX))) (PreH15 : (problem_28_pre_z rows )) (PreH16 : (total_prefix_state_28 rows i total )) (PreH17 : (0 < total)) (PreH18 : (total < INT_MAX)) ,
  (CharArray.undef_full retval total )
|--
  (CharArray.undef_full retval total )
.

Definition concatenate_entail_wit_8 := 
(
forall (strings_size_pre: Z) (strings_pre: Z) (rows: (@list (@list Z))) (out: Z) (k: Z) (out_l_2: (@list Z)) (total: Z) (len: Z) (len0: Z) (i: Z) (PreH1 : (i < strings_size_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= strings_size_pre)) (PreH4 : (0 <= strings_size_pre)) (PreH5 : (strings_size_pre <= 100)) (PreH6 : (0 <= len0)) (PreH7 : (len0 < INT_MAX)) (PreH8 : (0 <= len)) (PreH9 : (len < INT_MAX)) (PreH10 : (rows_well_formed_28 rows strings_size_pre )) (PreH11 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p_2)) + 1 ) < INT_MAX))) (PreH12 : (problem_28_pre_z rows )) (PreH13 : (total_prefix_state_28 rows strings_size_pre total )) (PreH14 : (copy_prefix_state_28 rows i k out_l_2 )) ,
  (CharPtrArray2.full strings_pre strings_size_pre rows )
  **  (CharArray.full out k out_l_2 )
  **  (CharArray.undef_seg out k total )
|--
  EX (row_ptr: Z)  (out_l: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i < strings_size_pre) ” 
  &&  “ (0 <= strings_size_pre) ” 
  &&  “ (strings_size_pre <= 100) ” 
  &&  “ (0 <= len0) ” 
  &&  “ (len0 < INT_MAX) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (rows_well_formed_28 rows strings_size_pre ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p)) + 1 ) < INT_MAX)) ” 
  &&  “ (problem_28_pre_z rows ) ” 
  &&  “ (total_prefix_state_28 rows strings_size_pre total ) ” 
  &&  “ (copy_prefix_state_28 rows i k out_l ) ” 
  &&  “ (valid_string (row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))) ) ” 
  &&  “ (all_ascii (row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))) ) ” 
  &&  “ ((string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX) ” 
  &&  “ ((Zlength ((Znth (i) (rows) ((@nil Z))))) = ((string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) + 1 )) ”
  &&  (CharPtrArray2.missing_i strings_pre strings_size_pre i row_ptr rows )
  **  (((strings_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))) )
  **  (CharArray.full out k out_l )
  **  (CharArray.undef_seg out k total )
) \/
(
forall (strings_size_pre: Z) (rows: (@list (@list Z))) (k: Z) (out_l_2: (@list Z)) (total: Z) (len: Z) (len0: Z) (i: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (0 <= (Zlength ((Znth i rows __default__List_Z))))) (PreH2 : (i < strings_size_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= strings_size_pre)) (PreH5 : (0 <= strings_size_pre)) (PreH6 : (strings_size_pre <= 100)) (PreH7 : (0 <= len0)) (PreH8 : (len0 < INT_MAX)) (PreH9 : (0 <= len)) (PreH10 : (len < INT_MAX)) (PreH11 : (rows_well_formed_28 rows strings_size_pre )) (PreH12 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p_2)) + 1 ) < INT_MAX))) (PreH13 : (problem_28_pre_z rows )) (PreH14 : (total_prefix_state_28 rows strings_size_pre total )) (PreH15 : (copy_prefix_state_28 rows i k out_l_2 )) ,
  (CharArray.full row_ptr_2 (Zlength ((Znth i rows __default__List_Z))) (Znth i rows __default__List_Z) )
|--
  “ ((Zlength ((Znth (i) (rows) ((@nil Z))))) = ((string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) + 1 )) ” 
  &&  “ ((string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX) ” 
  &&  “ (all_ascii (row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))) ) ” 
  &&  “ (valid_string (row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))) ) ”
  &&  (CharArray.full row_ptr_2 ((string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) )
).

Definition concatenate_entail_wit_8_split_goal_1 := 
forall (strings_size_pre: Z) (rows: (@list (@list Z))) (k: Z) (out_l_2: (@list Z)) (total: Z) (len: Z) (len0: Z) (i: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (0 <= (Zlength ((Znth i rows __default__List_Z))))) (PreH2 : (i < strings_size_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= strings_size_pre)) (PreH5 : (0 <= strings_size_pre)) (PreH6 : (strings_size_pre <= 100)) (PreH7 : (0 <= len0)) (PreH8 : (len0 < INT_MAX)) (PreH9 : (0 <= len)) (PreH10 : (len < INT_MAX)) (PreH11 : (rows_well_formed_28 rows strings_size_pre )) (PreH12 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p_2)) + 1 ) < INT_MAX))) (PreH13 : (problem_28_pre_z rows )) (PreH14 : (total_prefix_state_28 rows strings_size_pre total )) (PreH15 : (copy_prefix_state_28 rows i k out_l_2 )) ,
  (CharArray.full row_ptr_2 (Zlength ((Znth i rows __default__List_Z))) (Znth i rows __default__List_Z) )
|--
  “ ((Zlength ((Znth (i) (rows) ((@nil Z))))) = ((string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) + 1 )) ”
.

Definition concatenate_entail_wit_8_split_goal_2 := 
forall (strings_size_pre: Z) (rows: (@list (@list Z))) (k: Z) (out_l_2: (@list Z)) (total: Z) (len: Z) (len0: Z) (i: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (0 <= (Zlength ((Znth i rows __default__List_Z))))) (PreH2 : (i < strings_size_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= strings_size_pre)) (PreH5 : (0 <= strings_size_pre)) (PreH6 : (strings_size_pre <= 100)) (PreH7 : (0 <= len0)) (PreH8 : (len0 < INT_MAX)) (PreH9 : (0 <= len)) (PreH10 : (len < INT_MAX)) (PreH11 : (rows_well_formed_28 rows strings_size_pre )) (PreH12 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p_2)) + 1 ) < INT_MAX))) (PreH13 : (problem_28_pre_z rows )) (PreH14 : (total_prefix_state_28 rows strings_size_pre total )) (PreH15 : (copy_prefix_state_28 rows i k out_l_2 )) ,
  (CharArray.full row_ptr_2 (Zlength ((Znth i rows __default__List_Z))) (Znth i rows __default__List_Z) )
|--
  “ ((string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX) ”
.

Definition concatenate_entail_wit_8_split_goal_3 := 
forall (strings_size_pre: Z) (rows: (@list (@list Z))) (k: Z) (out_l_2: (@list Z)) (total: Z) (len: Z) (len0: Z) (i: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (0 <= (Zlength ((Znth i rows __default__List_Z))))) (PreH2 : (i < strings_size_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= strings_size_pre)) (PreH5 : (0 <= strings_size_pre)) (PreH6 : (strings_size_pre <= 100)) (PreH7 : (0 <= len0)) (PreH8 : (len0 < INT_MAX)) (PreH9 : (0 <= len)) (PreH10 : (len < INT_MAX)) (PreH11 : (rows_well_formed_28 rows strings_size_pre )) (PreH12 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p_2)) + 1 ) < INT_MAX))) (PreH13 : (problem_28_pre_z rows )) (PreH14 : (total_prefix_state_28 rows strings_size_pre total )) (PreH15 : (copy_prefix_state_28 rows i k out_l_2 )) ,
  (CharArray.full row_ptr_2 (Zlength ((Znth i rows __default__List_Z))) (Znth i rows __default__List_Z) )
|--
  “ (all_ascii (row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))) ) ”
.

Definition concatenate_entail_wit_8_split_goal_4 := 
forall (strings_size_pre: Z) (rows: (@list (@list Z))) (k: Z) (out_l_2: (@list Z)) (total: Z) (len: Z) (len0: Z) (i: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (0 <= (Zlength ((Znth i rows __default__List_Z))))) (PreH2 : (i < strings_size_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= strings_size_pre)) (PreH5 : (0 <= strings_size_pre)) (PreH6 : (strings_size_pre <= 100)) (PreH7 : (0 <= len0)) (PreH8 : (len0 < INT_MAX)) (PreH9 : (0 <= len)) (PreH10 : (len < INT_MAX)) (PreH11 : (rows_well_formed_28 rows strings_size_pre )) (PreH12 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p_2)) + 1 ) < INT_MAX))) (PreH13 : (problem_28_pre_z rows )) (PreH14 : (total_prefix_state_28 rows strings_size_pre total )) (PreH15 : (copy_prefix_state_28 rows i k out_l_2 )) ,
  (CharArray.full row_ptr_2 (Zlength ((Znth i rows __default__List_Z))) (Znth i rows __default__List_Z) )
|--
  “ (valid_string (row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))) ) ”
.

Definition concatenate_entail_wit_8_split_goal_spatial := 
forall (strings_size_pre: Z) (rows: (@list (@list Z))) (k: Z) (out_l_2: (@list Z)) (total: Z) (len: Z) (len0: Z) (i: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (0 <= (Zlength ((Znth i rows __default__List_Z))))) (PreH2 : (i < strings_size_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= strings_size_pre)) (PreH5 : (0 <= strings_size_pre)) (PreH6 : (strings_size_pre <= 100)) (PreH7 : (0 <= len0)) (PreH8 : (len0 < INT_MAX)) (PreH9 : (0 <= len)) (PreH10 : (len < INT_MAX)) (PreH11 : (rows_well_formed_28 rows strings_size_pre )) (PreH12 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p_2)) + 1 ) < INT_MAX))) (PreH13 : (problem_28_pre_z rows )) (PreH14 : (total_prefix_state_28 rows strings_size_pre total )) (PreH15 : (copy_prefix_state_28 rows i k out_l_2 )) ,
  (CharArray.full row_ptr_2 (Zlength ((Znth i rows __default__List_Z))) (Znth i rows __default__List_Z) )
|--
  (CharArray.full row_ptr_2 ((string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) )
.

Definition concatenate_entail_wit_9 := 
forall (strings_size_pre: Z) (strings_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (out_l_2: (@list Z)) (i: Z) (len0: Z) (len: Z) (total: Z) (k: Z) (out: Z) (PreH1 : (0 <= i)) (PreH2 : (i < strings_size_pre)) (PreH3 : (0 <= strings_size_pre)) (PreH4 : (strings_size_pre <= 100)) (PreH5 : (0 <= len0)) (PreH6 : (len0 < INT_MAX)) (PreH7 : (0 <= len)) (PreH8 : (len < INT_MAX)) (PreH9 : (rows_well_formed_28 rows strings_size_pre )) (PreH10 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p_2)) + 1 ) < INT_MAX))) (PreH11 : (problem_28_pre_z rows )) (PreH12 : (total_prefix_state_28 rows strings_size_pre total )) (PreH13 : (copy_prefix_state_28 rows i k out_l_2 )) (PreH14 : (valid_string (row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))) )) (PreH15 : (all_ascii (row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))) )) (PreH16 : ((string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX)) (PreH17 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = ((string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) ,
  (CharPtrArray2.missing_i strings_pre strings_size_pre i row_ptr rows )
  **  (((strings_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))) )
  **  (CharArray.full out k out_l_2 )
  **  (CharArray.undef_seg out k total )
|--
  EX (out_l: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i < strings_size_pre) ” 
  &&  “ (0 <= strings_size_pre) ” 
  &&  “ (strings_size_pre <= 100) ” 
  &&  “ (0 <= len0) ” 
  &&  “ (len0 < INT_MAX) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (rows_well_formed_28 rows strings_size_pre ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p)) + 1 ) < INT_MAX)) ” 
  &&  “ (problem_28_pre_z rows ) ” 
  &&  “ (total_prefix_state_28 rows strings_size_pre total ) ” 
  &&  “ (copy_prefix_state_28 rows i k out_l ) ” 
  &&  “ (valid_string (row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))) ) ” 
  &&  “ (all_ascii (row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))) ) ” 
  &&  “ ((string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX) ” 
  &&  “ ((Zlength ((Znth (i) (rows) ((@nil Z))))) = ((string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) + 1 )) ”
  &&  (CharPtrArray2.missing_i strings_pre strings_size_pre i row_ptr rows )
  **  (((strings_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))) )
  **  (CharArray.full out k out_l )
  **  (CharArray.undef_seg out k total )
.

Definition concatenate_entail_wit_10 := 
(
forall (strings_size_pre: Z) (strings_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (out_l_2: (@list Z)) (i: Z) (len0: Z) (len: Z) (total: Z) (k: Z) (out: Z) (retval: Z) (PreH1 : (retval = (string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))))) (PreH2 : (0 <= ((string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) (PreH3 : (0 <= k)) (PreH4 : (0 <= i)) (PreH5 : (i < strings_size_pre)) (PreH6 : (0 <= strings_size_pre)) (PreH7 : (strings_size_pre <= 100)) (PreH8 : (0 <= len0)) (PreH9 : (len0 < INT_MAX)) (PreH10 : (0 <= len)) (PreH11 : (len < INT_MAX)) (PreH12 : (rows_well_formed_28 rows strings_size_pre )) (PreH13 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p_2)) + 1 ) < INT_MAX))) (PreH14 : (problem_28_pre_z rows )) (PreH15 : (total_prefix_state_28 rows strings_size_pre total )) (PreH16 : (copy_prefix_state_28 rows i k out_l_2 )) (PreH17 : (valid_string (row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))) )) (PreH18 : (all_ascii (row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))) )) (PreH19 : ((string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX)) (PreH20 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = ((string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) ,
  (store_string row_ptr (row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))) )
  **  (CharPtrArray2.missing_i strings_pre strings_size_pre i row_ptr rows )
  **  (((strings_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full out k out_l_2 )
  **  (CharArray.undef_seg out k total )
|--
  EX (out_l: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i < strings_size_pre) ” 
  &&  “ (0 <= strings_size_pre) ” 
  &&  “ (strings_size_pre <= 100) ” 
  &&  “ (retval = (row_len_z_28 ((Znth (i) (rows) ((@nil Z)))))) ” 
  &&  “ ((k + retval ) < total) ” 
  &&  “ (0 <= len0) ” 
  &&  “ (len0 < INT_MAX) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < INT_MAX) ” 
  &&  “ (rows_well_formed_28 rows strings_size_pre ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p)) + 1 ) < INT_MAX)) ” 
  &&  “ (problem_28_pre_z rows ) ” 
  &&  “ (total_prefix_state_28 rows strings_size_pre total ) ” 
  &&  “ (copy_prefix_state_28 rows i k out_l ) ” 
  &&  “ (all_ascii (row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))) ) ” 
  &&  “ ((Zlength ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) = retval) ”
  &&  (CharPtrArray2.missing_i strings_pre strings_size_pre i row_ptr rows )
  **  (((strings_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr retval (row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))) )
  **  (CharArray.seg row_ptr retval (retval + 1 ) (cons (0) ((@nil Z))) )
  **  (CharArray.full out k out_l )
  **  (CharArray.undef_full (out + (k * sizeof(CHAR) ) ) retval )
  **  (CharArray.undef_seg out (k + retval ) total )
) \/
(
forall (strings_size_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (out_l_2: (@list Z)) (i: Z) (len0: Z) (len: Z) (total: Z) (k: Z) (out: Z) (retval: Z) (PreH1 : (retval = (string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))))) (PreH2 : (0 <= ((string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) (PreH3 : (0 <= k)) (PreH4 : (0 <= i)) (PreH5 : (i < strings_size_pre)) (PreH6 : (0 <= strings_size_pre)) (PreH7 : (strings_size_pre <= 100)) (PreH8 : (0 <= len0)) (PreH9 : (len0 < INT_MAX)) (PreH10 : (0 <= len)) (PreH11 : (len < INT_MAX)) (PreH12 : (rows_well_formed_28 rows strings_size_pre )) (PreH13 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p_2)) + 1 ) < INT_MAX))) (PreH14 : (problem_28_pre_z rows )) (PreH15 : (total_prefix_state_28 rows strings_size_pre total )) (PreH16 : (copy_prefix_state_28 rows i k out_l_2 )) (PreH17 : (valid_string (row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))) )) (PreH18 : (all_ascii (row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))) )) (PreH19 : ((string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX)) (PreH20 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = ((string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) ,
  (CharArray.full row_ptr ((string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) )
  **  (CharArray.undef_seg out k total )
|--
  “ ((Zlength ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) = retval) ” 
  &&  “ (0 <= retval) ” 
  &&  “ ((k + retval ) < total) ” 
  &&  “ (retval = (row_len_z_28 ((Znth (i) (rows) ((@nil Z)))))) ”
  &&  (CharArray.full row_ptr retval (row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))) )
  **  (CharArray.seg row_ptr retval (retval + 1 ) (cons (0) ((@nil Z))) )
  **  (CharArray.undef_full (out + (k * sizeof(CHAR) ) ) retval )
  **  (CharArray.undef_seg out (k + retval ) total )
).

Definition concatenate_entail_wit_10_split_goal_1 := 
forall (strings_size_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (out_l_2: (@list Z)) (i: Z) (len0: Z) (len: Z) (total: Z) (k: Z) (out: Z) (retval: Z) (PreH1 : (retval = (string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))))) (PreH2 : (0 <= ((string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) (PreH3 : (0 <= k)) (PreH4 : (0 <= i)) (PreH5 : (i < strings_size_pre)) (PreH6 : (0 <= strings_size_pre)) (PreH7 : (strings_size_pre <= 100)) (PreH8 : (0 <= len0)) (PreH9 : (len0 < INT_MAX)) (PreH10 : (0 <= len)) (PreH11 : (len < INT_MAX)) (PreH12 : (rows_well_formed_28 rows strings_size_pre )) (PreH13 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p_2)) + 1 ) < INT_MAX))) (PreH14 : (problem_28_pre_z rows )) (PreH15 : (total_prefix_state_28 rows strings_size_pre total )) (PreH16 : (copy_prefix_state_28 rows i k out_l_2 )) (PreH17 : (valid_string (row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))) )) (PreH18 : (all_ascii (row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))) )) (PreH19 : ((string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX)) (PreH20 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = ((string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) ,
  (CharArray.full row_ptr ((string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) )
  **  (CharArray.undef_seg out k total )
|--
  “ ((Zlength ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) = retval) ”
.

Definition concatenate_entail_wit_10_split_goal_2 := 
forall (strings_size_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (out_l_2: (@list Z)) (i: Z) (len0: Z) (len: Z) (total: Z) (k: Z) (out: Z) (retval: Z) (PreH1 : (retval = (string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))))) (PreH2 : (0 <= ((string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) (PreH3 : (0 <= k)) (PreH4 : (0 <= i)) (PreH5 : (i < strings_size_pre)) (PreH6 : (0 <= strings_size_pre)) (PreH7 : (strings_size_pre <= 100)) (PreH8 : (0 <= len0)) (PreH9 : (len0 < INT_MAX)) (PreH10 : (0 <= len)) (PreH11 : (len < INT_MAX)) (PreH12 : (rows_well_formed_28 rows strings_size_pre )) (PreH13 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p_2)) + 1 ) < INT_MAX))) (PreH14 : (problem_28_pre_z rows )) (PreH15 : (total_prefix_state_28 rows strings_size_pre total )) (PreH16 : (copy_prefix_state_28 rows i k out_l_2 )) (PreH17 : (valid_string (row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))) )) (PreH18 : (all_ascii (row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))) )) (PreH19 : ((string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX)) (PreH20 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = ((string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) ,
  (CharArray.full row_ptr ((string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) )
  **  (CharArray.undef_seg out k total )
|--
  “ (0 <= retval) ”
.

Definition concatenate_entail_wit_10_split_goal_3 := 
forall (strings_size_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (out_l_2: (@list Z)) (i: Z) (len0: Z) (len: Z) (total: Z) (k: Z) (out: Z) (retval: Z) (PreH1 : (retval = (string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))))) (PreH2 : (0 <= ((string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) (PreH3 : (0 <= k)) (PreH4 : (0 <= i)) (PreH5 : (i < strings_size_pre)) (PreH6 : (0 <= strings_size_pre)) (PreH7 : (strings_size_pre <= 100)) (PreH8 : (0 <= len0)) (PreH9 : (len0 < INT_MAX)) (PreH10 : (0 <= len)) (PreH11 : (len < INT_MAX)) (PreH12 : (rows_well_formed_28 rows strings_size_pre )) (PreH13 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p_2)) + 1 ) < INT_MAX))) (PreH14 : (problem_28_pre_z rows )) (PreH15 : (total_prefix_state_28 rows strings_size_pre total )) (PreH16 : (copy_prefix_state_28 rows i k out_l_2 )) (PreH17 : (valid_string (row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))) )) (PreH18 : (all_ascii (row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))) )) (PreH19 : ((string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX)) (PreH20 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = ((string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) ,
  (CharArray.full row_ptr ((string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) )
  **  (CharArray.undef_seg out k total )
|--
  “ ((k + retval ) < total) ”
.

Definition concatenate_entail_wit_10_split_goal_4 := 
forall (strings_size_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (out_l_2: (@list Z)) (i: Z) (len0: Z) (len: Z) (total: Z) (k: Z) (out: Z) (retval: Z) (PreH1 : (retval = (string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))))) (PreH2 : (0 <= ((string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) (PreH3 : (0 <= k)) (PreH4 : (0 <= i)) (PreH5 : (i < strings_size_pre)) (PreH6 : (0 <= strings_size_pre)) (PreH7 : (strings_size_pre <= 100)) (PreH8 : (0 <= len0)) (PreH9 : (len0 < INT_MAX)) (PreH10 : (0 <= len)) (PreH11 : (len < INT_MAX)) (PreH12 : (rows_well_formed_28 rows strings_size_pre )) (PreH13 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p_2)) + 1 ) < INT_MAX))) (PreH14 : (problem_28_pre_z rows )) (PreH15 : (total_prefix_state_28 rows strings_size_pre total )) (PreH16 : (copy_prefix_state_28 rows i k out_l_2 )) (PreH17 : (valid_string (row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))) )) (PreH18 : (all_ascii (row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))) )) (PreH19 : ((string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX)) (PreH20 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = ((string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) ,
  (CharArray.full row_ptr ((string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) )
  **  (CharArray.undef_seg out k total )
|--
  “ (retval = (row_len_z_28 ((Znth (i) (rows) ((@nil Z)))))) ”
.

Definition concatenate_entail_wit_10_split_goal_spatial := 
forall (strings_size_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (out_l_2: (@list Z)) (i: Z) (len0: Z) (len: Z) (total: Z) (k: Z) (out: Z) (retval: Z) (PreH1 : (retval = (string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))))) (PreH2 : (0 <= ((string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) (PreH3 : (0 <= k)) (PreH4 : (0 <= i)) (PreH5 : (i < strings_size_pre)) (PreH6 : (0 <= strings_size_pre)) (PreH7 : (strings_size_pre <= 100)) (PreH8 : (0 <= len0)) (PreH9 : (len0 < INT_MAX)) (PreH10 : (0 <= len)) (PreH11 : (len < INT_MAX)) (PreH12 : (rows_well_formed_28 rows strings_size_pre )) (PreH13 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p_2)) + 1 ) < INT_MAX))) (PreH14 : (problem_28_pre_z rows )) (PreH15 : (total_prefix_state_28 rows strings_size_pre total )) (PreH16 : (copy_prefix_state_28 rows i k out_l_2 )) (PreH17 : (valid_string (row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))) )) (PreH18 : (all_ascii (row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))) )) (PreH19 : ((string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX)) (PreH20 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = ((string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) ,
  (CharArray.full row_ptr ((string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) )
  **  (CharArray.undef_seg out k total )
|--
  (CharArray.full row_ptr retval (row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))) )
  **  (CharArray.seg row_ptr retval (retval + 1 ) (cons (0) ((@nil Z))) )
  **  (CharArray.undef_full (out + (k * sizeof(CHAR) ) ) retval )
  **  (CharArray.undef_seg out (k + retval ) total )
.

Definition concatenate_entail_wit_11 := 
(
forall (strings_size_pre: Z) (strings_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (out_l_2: (@list Z)) (i: Z) (len: Z) (k: Z) (total: Z) (len0: Z) (out: Z) (retval: Z) (PreH1 : (retval = (out + (k * sizeof(CHAR) ) ))) (PreH2 : (0 <= k)) (PreH3 : (0 <= i)) (PreH4 : (i < strings_size_pre)) (PreH5 : (0 <= strings_size_pre)) (PreH6 : (strings_size_pre <= 100)) (PreH7 : (len = (row_len_z_28 ((Znth (i) (rows) ((@nil Z))))))) (PreH8 : ((k + len ) < total)) (PreH9 : (0 <= len0)) (PreH10 : (len0 < INT_MAX)) (PreH11 : (0 <= len)) (PreH12 : (len < INT_MAX)) (PreH13 : (rows_well_formed_28 rows strings_size_pre )) (PreH14 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p_2)) + 1 ) < INT_MAX))) (PreH15 : (problem_28_pre_z rows )) (PreH16 : (total_prefix_state_28 rows strings_size_pre total )) (PreH17 : (copy_prefix_state_28 rows i k out_l_2 )) (PreH18 : (all_ascii (row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))) )) (PreH19 : ((Zlength ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) = len)) ,
  (CharArray.full (out + (k * sizeof(CHAR) ) ) len (row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))) )
  **  (CharArray.full row_ptr len (row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))) )
  **  (CharPtrArray2.missing_i strings_pre strings_size_pre i row_ptr rows )
  **  (((strings_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.seg row_ptr len (len + 1 ) (cons (0) ((@nil Z))) )
  **  (CharArray.full out k out_l_2 )
  **  (CharArray.undef_seg out (k + len ) total )
|--
  EX (out_l: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i < strings_size_pre) ” 
  &&  “ (0 <= strings_size_pre) ” 
  &&  “ (strings_size_pre <= 100) ” 
  &&  “ (0 <= len0) ” 
  &&  “ (len0 < INT_MAX) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (rows_well_formed_28 rows strings_size_pre ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p)) + 1 ) < INT_MAX)) ” 
  &&  “ (problem_28_pre_z rows ) ” 
  &&  “ (total_prefix_state_28 rows strings_size_pre total ) ” 
  &&  “ (copy_prefix_state_28 rows (i + 1 ) (k + len ) out_l ) ”
  &&  (CharPtrArray2.full strings_pre strings_size_pre rows )
  **  (CharArray.full out (k + len ) out_l )
  **  (CharArray.undef_seg out (k + len ) total )
) \/
(
forall (strings_size_pre: Z) (strings_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (out_l_2: (@list Z)) (i: Z) (len: Z) (k: Z) (total: Z) (len0: Z) (out: Z) (retval: Z) (PreH1 : (retval = (out + (k * sizeof(CHAR) ) ))) (PreH2 : (0 <= k)) (PreH3 : (0 <= i)) (PreH4 : (i < strings_size_pre)) (PreH5 : (0 <= strings_size_pre)) (PreH6 : (strings_size_pre <= 100)) (PreH7 : (len = (row_len_z_28 ((Znth (i) (rows) ((@nil Z))))))) (PreH8 : ((k + len ) < total)) (PreH9 : (0 <= len0)) (PreH10 : (len0 < INT_MAX)) (PreH11 : (0 <= len)) (PreH12 : (len < INT_MAX)) (PreH13 : (rows_well_formed_28 rows strings_size_pre )) (PreH14 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p_2)) + 1 ) < INT_MAX))) (PreH15 : (problem_28_pre_z rows )) (PreH16 : (total_prefix_state_28 rows strings_size_pre total )) (PreH17 : (copy_prefix_state_28 rows i k out_l_2 )) (PreH18 : (all_ascii (row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))) )) (PreH19 : ((Zlength ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) = len)) ,
  (CharArray.full (out + (k * sizeof(CHAR) ) ) len (row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))) )
  **  (CharArray.full row_ptr len (row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))) )
  **  (CharPtrArray2.missing_i strings_pre strings_size_pre i row_ptr rows )
  **  (((strings_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.seg row_ptr len (len + 1 ) (cons (0) ((@nil Z))) )
  **  (CharArray.full out k out_l_2 )
|--
  EX (out_l: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i < strings_size_pre) ” 
  &&  “ (0 <= strings_size_pre) ” 
  &&  “ (strings_size_pre <= 100) ” 
  &&  “ (0 <= len0) ” 
  &&  “ (len0 < INT_MAX) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (rows_well_formed_28 rows strings_size_pre ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p)) + 1 ) < INT_MAX)) ” 
  &&  “ (problem_28_pre_z rows ) ” 
  &&  “ (total_prefix_state_28 rows strings_size_pre total ) ” 
  &&  “ (copy_prefix_state_28 rows (i + 1 ) (k + len ) out_l ) ”
  &&  (CharPtrArray2.full strings_pre strings_size_pre rows )
  **  (CharArray.full out (k + len ) out_l )
).

Definition concatenate_entail_wit_12 := 
forall (strings_size_pre: Z) (strings_pre: Z) (rows: (@list (@list Z))) (out_l_2: (@list Z)) (i: Z) (len0: Z) (len: Z) (total: Z) (k: Z) (out: Z) (PreH1 : (0 <= i)) (PreH2 : (i < strings_size_pre)) (PreH3 : (0 <= strings_size_pre)) (PreH4 : (strings_size_pre <= 100)) (PreH5 : (0 <= len0)) (PreH6 : (len0 < INT_MAX)) (PreH7 : (0 <= len)) (PreH8 : (len < INT_MAX)) (PreH9 : (rows_well_formed_28 rows strings_size_pre )) (PreH10 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p_2)) + 1 ) < INT_MAX))) (PreH11 : (problem_28_pre_z rows )) (PreH12 : (total_prefix_state_28 rows strings_size_pre total )) (PreH13 : (copy_prefix_state_28 rows (i + 1 ) k out_l_2 )) ,
  (CharPtrArray2.full strings_pre strings_size_pre rows )
  **  (CharArray.full out k out_l_2 )
  **  (CharArray.undef_seg out k total )
|--
  EX (out_l: (@list Z)) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= strings_size_pre) ” 
  &&  “ (0 <= strings_size_pre) ” 
  &&  “ (strings_size_pre <= 100) ” 
  &&  “ (0 <= len0) ” 
  &&  “ (len0 < INT_MAX) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (rows_well_formed_28 rows strings_size_pre ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p)) + 1 ) < INT_MAX)) ” 
  &&  “ (problem_28_pre_z rows ) ” 
  &&  “ (total_prefix_state_28 rows strings_size_pre total ) ” 
  &&  “ (copy_prefix_state_28 rows (i + 1 ) k out_l ) ”
  &&  (CharPtrArray2.full strings_pre strings_size_pre rows )
  **  (CharArray.full out k out_l )
  **  (CharArray.undef_seg out k total )
.

Definition concatenate_entail_wit_13 := 
(
forall (strings_size_pre: Z) (strings_pre: Z) (rows: (@list (@list Z))) (out: Z) (k: Z) (out_l_2: (@list Z)) (total: Z) (len: Z) (len0: Z) (i: Z) (PreH1 : (i >= strings_size_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= strings_size_pre)) (PreH4 : (0 <= strings_size_pre)) (PreH5 : (strings_size_pre <= 100)) (PreH6 : (0 <= len0)) (PreH7 : (len0 < INT_MAX)) (PreH8 : (0 <= len)) (PreH9 : (len < INT_MAX)) (PreH10 : (rows_well_formed_28 rows strings_size_pre )) (PreH11 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p_2)) + 1 ) < INT_MAX))) (PreH12 : (problem_28_pre_z rows )) (PreH13 : (total_prefix_state_28 rows strings_size_pre total )) (PreH14 : (copy_prefix_state_28 rows i k out_l_2 )) ,
  (CharPtrArray2.full strings_pre strings_size_pre rows )
  **  (CharArray.full out k out_l_2 )
  **  (CharArray.undef_seg out k total )
|--
  EX (out_l: (@list Z)) ,
  “ ((k + 1 ) = total) ” 
  &&  “ (rows_well_formed_28 rows strings_size_pre ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p)) + 1 ) < INT_MAX)) ” 
  &&  “ (0 <= len0) ” 
  &&  “ (len0 < INT_MAX) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (problem_28_pre_z rows ) ” 
  &&  “ (copy_prefix_state_28 rows strings_size_pre k out_l ) ”
  &&  (CharPtrArray2.full strings_pre strings_size_pre rows )
  **  (CharArray.full out k out_l )
  **  (CharArray.undef_seg out k (k + 1 ) )
) \/
(
forall (strings_size_pre: Z) (rows: (@list (@list Z))) (out: Z) (k: Z) (out_l_2: (@list Z)) (total: Z) (len: Z) (len0: Z) (i: Z) (PreH1 : (i >= strings_size_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= strings_size_pre)) (PreH4 : (0 <= strings_size_pre)) (PreH5 : (strings_size_pre <= 100)) (PreH6 : (0 <= len0)) (PreH7 : (len0 < INT_MAX)) (PreH8 : (0 <= len)) (PreH9 : (len < INT_MAX)) (PreH10 : (rows_well_formed_28 rows strings_size_pre )) (PreH11 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p_2)) + 1 ) < INT_MAX))) (PreH12 : (problem_28_pre_z rows )) (PreH13 : (total_prefix_state_28 rows strings_size_pre total )) (PreH14 : (copy_prefix_state_28 rows i k out_l_2 )) ,
  (CharArray.undef_seg out k total )
|--
  “ (copy_prefix_state_28 rows strings_size_pre k out_l_2 ) ” 
  &&  “ ((k + 1 ) = total) ”
  &&  (CharArray.undef_seg out k (k + 1 ) )
).

Definition concatenate_entail_wit_13_split_goal_1 := 
forall (strings_size_pre: Z) (rows: (@list (@list Z))) (out: Z) (k: Z) (out_l_2: (@list Z)) (total: Z) (len: Z) (len0: Z) (i: Z) (PreH1 : (i >= strings_size_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= strings_size_pre)) (PreH4 : (0 <= strings_size_pre)) (PreH5 : (strings_size_pre <= 100)) (PreH6 : (0 <= len0)) (PreH7 : (len0 < INT_MAX)) (PreH8 : (0 <= len)) (PreH9 : (len < INT_MAX)) (PreH10 : (rows_well_formed_28 rows strings_size_pre )) (PreH11 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p_2)) + 1 ) < INT_MAX))) (PreH12 : (problem_28_pre_z rows )) (PreH13 : (total_prefix_state_28 rows strings_size_pre total )) (PreH14 : (copy_prefix_state_28 rows i k out_l_2 )) ,
  (CharArray.undef_seg out k total )
|--
  “ (copy_prefix_state_28 rows strings_size_pre k out_l_2 ) ”
.

Definition concatenate_entail_wit_13_split_goal_2 := 
forall (strings_size_pre: Z) (rows: (@list (@list Z))) (out: Z) (k: Z) (out_l_2: (@list Z)) (total: Z) (len: Z) (len0: Z) (i: Z) (PreH1 : (i >= strings_size_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= strings_size_pre)) (PreH4 : (0 <= strings_size_pre)) (PreH5 : (strings_size_pre <= 100)) (PreH6 : (0 <= len0)) (PreH7 : (len0 < INT_MAX)) (PreH8 : (0 <= len)) (PreH9 : (len < INT_MAX)) (PreH10 : (rows_well_formed_28 rows strings_size_pre )) (PreH11 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p_2)) + 1 ) < INT_MAX))) (PreH12 : (problem_28_pre_z rows )) (PreH13 : (total_prefix_state_28 rows strings_size_pre total )) (PreH14 : (copy_prefix_state_28 rows i k out_l_2 )) ,
  (CharArray.undef_seg out k total )
|--
  “ ((k + 1 ) = total) ”
.

Definition concatenate_entail_wit_13_split_goal_spatial := 
forall (strings_size_pre: Z) (rows: (@list (@list Z))) (out: Z) (k: Z) (out_l_2: (@list Z)) (total: Z) (len: Z) (len0: Z) (i: Z) (PreH1 : (i >= strings_size_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= strings_size_pre)) (PreH4 : (0 <= strings_size_pre)) (PreH5 : (strings_size_pre <= 100)) (PreH6 : (0 <= len0)) (PreH7 : (len0 < INT_MAX)) (PreH8 : (0 <= len)) (PreH9 : (len < INT_MAX)) (PreH10 : (rows_well_formed_28 rows strings_size_pre )) (PreH11 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p_2)) + 1 ) < INT_MAX))) (PreH12 : (problem_28_pre_z rows )) (PreH13 : (total_prefix_state_28 rows strings_size_pre total )) (PreH14 : (copy_prefix_state_28 rows i k out_l_2 )) ,
  (CharArray.undef_seg out k total )
|--
  (CharArray.undef_seg out k (k + 1 ) )
.

Definition concatenate_entail_wit_14 := 
(
forall (strings_size_pre: Z) (strings_pre: Z) (rows: (@list (@list Z))) (out_l_2: (@list Z)) (k: Z) (total: Z) (len0: Z) (len: Z) (out: Z) (PreH1 : (0 <= k)) (PreH2 : ((k + 1 ) = total)) (PreH3 : (rows_well_formed_28 rows strings_size_pre )) (PreH4 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p_2)) + 1 ) < INT_MAX))) (PreH5 : (0 <= len0)) (PreH6 : (len0 < INT_MAX)) (PreH7 : (0 <= len)) (PreH8 : (len < INT_MAX)) (PreH9 : (problem_28_pre_z rows )) (PreH10 : (copy_prefix_state_28 rows strings_size_pre k out_l_2 )) ,
  (CharArray.full out (k + 1 ) (app (out_l_2) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out (k + 1 ) (k + 1 ) )
  **  (CharPtrArray2.full strings_pre strings_size_pre rows )
|--
  EX (out_l: (@list Z)) ,
  “ ((k + 1 ) = total) ” 
  &&  “ (rows_well_formed_28 rows strings_size_pre ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p)) + 1 ) < INT_MAX)) ” 
  &&  “ (0 <= len0) ” 
  &&  “ (len0 < INT_MAX) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (problem_28_pre_z rows ) ” 
  &&  “ (copy_prefix_state_28 rows strings_size_pre k out_l ) ” 
  &&  “ (problem_28_spec_z rows out_l ) ”
  &&  (CharPtrArray2.full strings_pre strings_size_pre rows )
  **  (CharArray.full out (k + 1 ) (app (out_l) ((cons (0) ((@nil Z))))) )
) \/
(
forall (strings_size_pre: Z) (rows: (@list (@list Z))) (out_l_2: (@list Z)) (k: Z) (total: Z) (len0: Z) (len: Z) (PreH1 : (0 <= k)) (PreH2 : ((k + 1 ) = total)) (PreH3 : (rows_well_formed_28 rows strings_size_pre )) (PreH4 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p_2)) + 1 ) < INT_MAX))) (PreH5 : (0 <= len0)) (PreH6 : (len0 < INT_MAX)) (PreH7 : (0 <= len)) (PreH8 : (len < INT_MAX)) (PreH9 : (problem_28_pre_z rows )) (PreH10 : (copy_prefix_state_28 rows strings_size_pre k out_l_2 )) ,
  TT && emp 
|--
  EX (out_l: (@list Z)) ,
  “ ((app (out_l_2) ((cons (0) ((@nil Z))))) = (app (out_l) ((cons (0) ((@nil Z)))))) ” 
  &&  “ ((k + 1 ) = total) ” 
  &&  “ (rows_well_formed_28 rows strings_size_pre ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p)) + 1 ) < INT_MAX)) ” 
  &&  “ (0 <= len0) ” 
  &&  “ (len0 < INT_MAX) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (problem_28_pre_z rows ) ” 
  &&  “ (copy_prefix_state_28 rows strings_size_pre k out_l ) ” 
  &&  “ (problem_28_spec_z rows out_l ) ”
  &&  emp
).

Definition concatenate_return_wit_1 := 
(
forall (strings_size_pre: Z) (strings_pre: Z) (rows: (@list (@list Z))) (out_l_2: (@list Z)) (k: Z) (total: Z) (len0: Z) (len: Z) (out: Z) (PreH1 : ((k + 1 ) = total)) (PreH2 : (rows_well_formed_28 rows strings_size_pre )) (PreH3 : forall (p: Z) , (((0 <= p) /\ (p <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p)) + 1 ) < INT_MAX))) (PreH4 : (0 <= len0)) (PreH5 : (len0 < INT_MAX)) (PreH6 : (0 <= len)) (PreH7 : (len < INT_MAX)) (PreH8 : (problem_28_pre_z rows )) (PreH9 : (copy_prefix_state_28 rows strings_size_pre k out_l_2 )) (PreH10 : (problem_28_spec_z rows out_l_2 )) ,
  (CharPtrArray2.full strings_pre strings_size_pre rows )
  **  (CharArray.full out (k + 1 ) (app (out_l_2) ((cons (0) ((@nil Z))))) )
|--
  EX (out_l: (@list Z)) ,
  “ (problem_28_spec_z rows out_l ) ”
  &&  (CharPtrArray2.full strings_pre strings_size_pre rows )
  **  (CharArray.full out ((Zlength (out_l)) + 1 ) (app (out_l) ((cons (0) ((@nil Z))))) )
) \/
(
forall (strings_size_pre: Z) (rows: (@list (@list Z))) (out_l_2: (@list Z)) (k: Z) (total: Z) (len0: Z) (len: Z) (out: Z) (PreH1 : (0 <= (k + 1 ))) (PreH2 : ((k + 1 ) = total)) (PreH3 : (rows_well_formed_28 rows strings_size_pre )) (PreH4 : forall (p: Z) , (((0 <= p) /\ (p <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p)) + 1 ) < INT_MAX))) (PreH5 : (0 <= len0)) (PreH6 : (len0 < INT_MAX)) (PreH7 : (0 <= len)) (PreH8 : (len < INT_MAX)) (PreH9 : (problem_28_pre_z rows )) (PreH10 : (copy_prefix_state_28 rows strings_size_pre k out_l_2 )) (PreH11 : (problem_28_spec_z rows out_l_2 )) ,
  (CharArray.full out (k + 1 ) (app (out_l_2) ((cons (0) ((@nil Z))))) )
|--
  EX (out_l: (@list Z)) ,
  “ (problem_28_spec_z rows out_l ) ”
  &&  (CharArray.full out ((Zlength (out_l)) + 1 ) (app (out_l) ((cons (0) ((@nil Z))))) )
).

Definition concatenate_partial_solve_wit_1_pure := 
forall (strings_size_pre: Z) (strings_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (i: Z) (out: Z) (k: Z) (len0: Z) (len: Z) (total: Z) (PreH1 : (0 <= i)) (PreH2 : (i < strings_size_pre)) (PreH3 : (0 <= strings_size_pre)) (PreH4 : (strings_size_pre <= 100)) (PreH5 : (out = 0)) (PreH6 : (k = 0)) (PreH7 : (0 <= len0)) (PreH8 : (len0 < INT_MAX)) (PreH9 : (0 <= len)) (PreH10 : (len < INT_MAX)) (PreH11 : (rows_well_formed_28 rows strings_size_pre )) (PreH12 : forall (p: Z) , (((0 <= p) /\ (p <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p)) + 1 ) < INT_MAX))) (PreH13 : (problem_28_pre_z rows )) (PreH14 : (total_prefix_state_28 rows i total )) (PreH15 : (valid_string (row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))) )) (PreH16 : ((string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX)) (PreH17 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = ((string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "strings_size" ) )) # Int  |-> strings_size_pre)
  **  ((( &( "strings" ) )) # Ptr  |-> strings_pre)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "len0" ) )) # Int  |-> len0)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  (CharPtrArray2.missing_i strings_pre strings_size_pre i row_ptr rows )
  **  (((strings_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))) )
|--
  “ (valid_string (row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))) ) ” 
  &&  “ ((string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX) ”
.

Definition concatenate_partial_solve_wit_1_aux := 
forall (strings_size_pre: Z) (strings_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (i: Z) (out: Z) (k: Z) (len0: Z) (len: Z) (total: Z) (PreH1 : (0 <= i)) (PreH2 : (i < strings_size_pre)) (PreH3 : (0 <= strings_size_pre)) (PreH4 : (strings_size_pre <= 100)) (PreH5 : (out = 0)) (PreH6 : (k = 0)) (PreH7 : (0 <= len0)) (PreH8 : (len0 < INT_MAX)) (PreH9 : (0 <= len)) (PreH10 : (len < INT_MAX)) (PreH11 : (rows_well_formed_28 rows strings_size_pre )) (PreH12 : forall (p: Z) , (((0 <= p) /\ (p <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p)) + 1 ) < INT_MAX))) (PreH13 : (problem_28_pre_z rows )) (PreH14 : (total_prefix_state_28 rows i total )) (PreH15 : (valid_string (row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))) )) (PreH16 : ((string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX)) (PreH17 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = ((string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) ,
  (CharPtrArray2.missing_i strings_pre strings_size_pre i row_ptr rows )
  **  (((strings_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))) )
|--
  “ (valid_string (row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))) ) ” 
  &&  “ ((string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX) ” 
  &&  “ (0 <= ((string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < strings_size_pre) ” 
  &&  “ (0 <= strings_size_pre) ” 
  &&  “ (strings_size_pre <= 100) ” 
  &&  “ (out = 0) ” 
  &&  “ (k = 0) ” 
  &&  “ (0 <= len0) ” 
  &&  “ (len0 < INT_MAX) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (rows_well_formed_28 rows strings_size_pre ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p)) + 1 ) < INT_MAX)) ” 
  &&  “ (problem_28_pre_z rows ) ” 
  &&  “ (total_prefix_state_28 rows i total ) ” 
  &&  “ (valid_string (row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))) ) ” 
  &&  “ ((string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX) ” 
  &&  “ ((Zlength ((Znth (i) (rows) ((@nil Z))))) = ((string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) + 1 )) ”
  &&  (store_string row_ptr (row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))) )
  **  (CharPtrArray2.missing_i strings_pre strings_size_pre i row_ptr rows )
  **  (((strings_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
.

Definition concatenate_partial_solve_wit_1 := concatenate_partial_solve_wit_1_pure -> concatenate_partial_solve_wit_1_aux.

Definition concatenate_partial_solve_wit_2_pure := 
forall (strings_size_pre: Z) (strings_pre: Z) (rows: (@list (@list Z))) (total: Z) (len: Z) (len0: Z) (cur: Z) (k: Z) (out: Z) (i: Z) (PreH1 : (i >= strings_size_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= strings_size_pre)) (PreH4 : (0 <= strings_size_pre)) (PreH5 : (strings_size_pre <= 100)) (PreH6 : (out = 0)) (PreH7 : (k = 0)) (PreH8 : (0 <= len0)) (PreH9 : (len0 < INT_MAX)) (PreH10 : (0 <= len)) (PreH11 : (len < INT_MAX)) (PreH12 : (rows_well_formed_28 rows strings_size_pre )) (PreH13 : forall (p: Z) , (((0 <= p) /\ (p <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p)) + 1 ) < INT_MAX))) (PreH14 : (problem_28_pre_z rows )) (PreH15 : (total_prefix_state_28 rows i total )) (PreH16 : (0 < total)) (PreH17 : (total < INT_MAX)) ,
  ((( &( "strings_size" ) )) # Int  |-> strings_size_pre)
  **  ((( &( "strings" ) )) # Ptr  |-> strings_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "len0" ) )) # Int  |-> len0)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  (CharPtrArray2.full strings_pre strings_size_pre rows )
|--
  “ (total > 0) ” 
  &&  “ (total < INT_MAX) ”
.

Definition concatenate_partial_solve_wit_2_aux := 
forall (strings_size_pre: Z) (strings_pre: Z) (rows: (@list (@list Z))) (total: Z) (len: Z) (len0: Z) (k: Z) (out: Z) (i: Z) (PreH1 : (i >= strings_size_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= strings_size_pre)) (PreH4 : (0 <= strings_size_pre)) (PreH5 : (strings_size_pre <= 100)) (PreH6 : (out = 0)) (PreH7 : (k = 0)) (PreH8 : (0 <= len0)) (PreH9 : (len0 < INT_MAX)) (PreH10 : (0 <= len)) (PreH11 : (len < INT_MAX)) (PreH12 : (rows_well_formed_28 rows strings_size_pre )) (PreH13 : forall (p: Z) , (((0 <= p) /\ (p <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p)) + 1 ) < INT_MAX))) (PreH14 : (problem_28_pre_z rows )) (PreH15 : (total_prefix_state_28 rows i total )) (PreH16 : (0 < total)) (PreH17 : (total < INT_MAX)) ,
  (CharPtrArray2.full strings_pre strings_size_pre rows )
|--
  “ (total > 0) ” 
  &&  “ (total < INT_MAX) ” 
  &&  “ (i >= strings_size_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= strings_size_pre) ” 
  &&  “ (0 <= strings_size_pre) ” 
  &&  “ (strings_size_pre <= 100) ” 
  &&  “ (out = 0) ” 
  &&  “ (k = 0) ” 
  &&  “ (0 <= len0) ” 
  &&  “ (len0 < INT_MAX) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (rows_well_formed_28 rows strings_size_pre ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p)) + 1 ) < INT_MAX)) ” 
  &&  “ (problem_28_pre_z rows ) ” 
  &&  “ (total_prefix_state_28 rows i total ) ” 
  &&  “ (0 < total) ” 
  &&  “ (total < INT_MAX) ”
  &&  (CharPtrArray2.full strings_pre strings_size_pre rows )
.

Definition concatenate_partial_solve_wit_2 := concatenate_partial_solve_wit_2_pure -> concatenate_partial_solve_wit_2_aux.

Definition concatenate_partial_solve_wit_3_pure := 
forall (strings_size_pre: Z) (strings_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (out_l: (@list Z)) (i: Z) (len0: Z) (len: Z) (total: Z) (k: Z) (out: Z) (PreH1 : (0 <= i)) (PreH2 : (i < strings_size_pre)) (PreH3 : (0 <= strings_size_pre)) (PreH4 : (strings_size_pre <= 100)) (PreH5 : (0 <= len0)) (PreH6 : (len0 < INT_MAX)) (PreH7 : (0 <= len)) (PreH8 : (len < INT_MAX)) (PreH9 : (rows_well_formed_28 rows strings_size_pre )) (PreH10 : forall (p: Z) , (((0 <= p) /\ (p <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p)) + 1 ) < INT_MAX))) (PreH11 : (problem_28_pre_z rows )) (PreH12 : (total_prefix_state_28 rows strings_size_pre total )) (PreH13 : (copy_prefix_state_28 rows i k out_l )) (PreH14 : (valid_string (row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))) )) (PreH15 : (all_ascii (row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))) )) (PreH16 : ((string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX)) (PreH17 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = ((string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "strings_size" ) )) # Int  |-> strings_size_pre)
  **  ((( &( "strings" ) )) # Ptr  |-> strings_pre)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "len0" ) )) # Int  |-> len0)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (CharPtrArray2.missing_i strings_pre strings_size_pre i row_ptr rows )
  **  (((strings_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out k out_l )
  **  (CharArray.undef_seg out k total )
|--
  “ (valid_string (row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))) ) ” 
  &&  “ ((string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX) ”
.

Definition concatenate_partial_solve_wit_3_aux := 
forall (strings_size_pre: Z) (strings_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (out_l: (@list Z)) (i: Z) (len0: Z) (len: Z) (total: Z) (k: Z) (out: Z) (PreH1 : (0 <= i)) (PreH2 : (i < strings_size_pre)) (PreH3 : (0 <= strings_size_pre)) (PreH4 : (strings_size_pre <= 100)) (PreH5 : (0 <= len0)) (PreH6 : (len0 < INT_MAX)) (PreH7 : (0 <= len)) (PreH8 : (len < INT_MAX)) (PreH9 : (rows_well_formed_28 rows strings_size_pre )) (PreH10 : forall (p: Z) , (((0 <= p) /\ (p <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p)) + 1 ) < INT_MAX))) (PreH11 : (problem_28_pre_z rows )) (PreH12 : (total_prefix_state_28 rows strings_size_pre total )) (PreH13 : (copy_prefix_state_28 rows i k out_l )) (PreH14 : (valid_string (row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))) )) (PreH15 : (all_ascii (row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))) )) (PreH16 : ((string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX)) (PreH17 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = ((string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) ,
  (CharPtrArray2.missing_i strings_pre strings_size_pre i row_ptr rows )
  **  (((strings_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))) )
  **  (CharArray.full out k out_l )
  **  (CharArray.undef_seg out k total )
|--
  “ (valid_string (row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))) ) ” 
  &&  “ ((string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX) ” 
  &&  “ (0 <= ((string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) + 1 )) ” 
  &&  “ (0 <= k) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < strings_size_pre) ” 
  &&  “ (0 <= strings_size_pre) ” 
  &&  “ (strings_size_pre <= 100) ” 
  &&  “ (0 <= len0) ” 
  &&  “ (len0 < INT_MAX) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (rows_well_formed_28 rows strings_size_pre ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p)) + 1 ) < INT_MAX)) ” 
  &&  “ (problem_28_pre_z rows ) ” 
  &&  “ (total_prefix_state_28 rows strings_size_pre total ) ” 
  &&  “ (copy_prefix_state_28 rows i k out_l ) ” 
  &&  “ (valid_string (row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))) ) ” 
  &&  “ (all_ascii (row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))) ) ” 
  &&  “ ((string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX) ” 
  &&  “ ((Zlength ((Znth (i) (rows) ((@nil Z))))) = ((string_length ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) + 1 )) ”
  &&  (store_string row_ptr (row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))) )
  **  (CharPtrArray2.missing_i strings_pre strings_size_pre i row_ptr rows )
  **  (((strings_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full out k out_l )
  **  (CharArray.undef_seg out k total )
.

Definition concatenate_partial_solve_wit_3 := concatenate_partial_solve_wit_3_pure -> concatenate_partial_solve_wit_3_aux.

Definition concatenate_partial_solve_wit_4_pure := 
forall (strings_size_pre: Z) (strings_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (out_l: (@list Z)) (i: Z) (len: Z) (k: Z) (total: Z) (len0: Z) (out: Z) (PreH1 : (0 <= i)) (PreH2 : (i < strings_size_pre)) (PreH3 : (0 <= strings_size_pre)) (PreH4 : (strings_size_pre <= 100)) (PreH5 : (len = (row_len_z_28 ((Znth (i) (rows) ((@nil Z))))))) (PreH6 : ((k + len ) < total)) (PreH7 : (0 <= len0)) (PreH8 : (len0 < INT_MAX)) (PreH9 : (0 <= len)) (PreH10 : (len < INT_MAX)) (PreH11 : (rows_well_formed_28 rows strings_size_pre )) (PreH12 : forall (p: Z) , (((0 <= p) /\ (p <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p)) + 1 ) < INT_MAX))) (PreH13 : (problem_28_pre_z rows )) (PreH14 : (total_prefix_state_28 rows strings_size_pre total )) (PreH15 : (copy_prefix_state_28 rows i k out_l )) (PreH16 : (all_ascii (row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))) )) (PreH17 : ((Zlength ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) = len)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "strings_size" ) )) # Int  |-> strings_size_pre)
  **  ((( &( "strings" ) )) # Ptr  |-> strings_pre)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "len0" ) )) # Int  |-> len0)
  **  (CharPtrArray2.missing_i strings_pre strings_size_pre i row_ptr rows )
  **  (((strings_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr len (row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))) )
  **  (CharArray.seg row_ptr len (len + 1 ) (cons (0) ((@nil Z))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out k out_l )
  **  (CharArray.undef_full (out + (k * sizeof(CHAR) ) ) len )
  **  (CharArray.undef_seg out (k + len ) total )
|--
  “ (all_ascii (row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))) ) ” 
  &&  “ ((Zlength ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) = len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ”
.

Definition concatenate_partial_solve_wit_4_aux := 
forall (strings_size_pre: Z) (strings_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (out_l: (@list Z)) (i: Z) (len: Z) (k: Z) (total: Z) (len0: Z) (out: Z) (PreH1 : (0 <= i)) (PreH2 : (i < strings_size_pre)) (PreH3 : (0 <= strings_size_pre)) (PreH4 : (strings_size_pre <= 100)) (PreH5 : (len = (row_len_z_28 ((Znth (i) (rows) ((@nil Z))))))) (PreH6 : ((k + len ) < total)) (PreH7 : (0 <= len0)) (PreH8 : (len0 < INT_MAX)) (PreH9 : (0 <= len)) (PreH10 : (len < INT_MAX)) (PreH11 : (rows_well_formed_28 rows strings_size_pre )) (PreH12 : forall (p: Z) , (((0 <= p) /\ (p <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p)) + 1 ) < INT_MAX))) (PreH13 : (problem_28_pre_z rows )) (PreH14 : (total_prefix_state_28 rows strings_size_pre total )) (PreH15 : (copy_prefix_state_28 rows i k out_l )) (PreH16 : (all_ascii (row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))) )) (PreH17 : ((Zlength ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) = len)) ,
  (CharPtrArray2.missing_i strings_pre strings_size_pre i row_ptr rows )
  **  (((strings_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr len (row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))) )
  **  (CharArray.seg row_ptr len (len + 1 ) (cons (0) ((@nil Z))) )
  **  (CharArray.full out k out_l )
  **  (CharArray.undef_full (out + (k * sizeof(CHAR) ) ) len )
  **  (CharArray.undef_seg out (k + len ) total )
|--
  “ (all_ascii (row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))) ) ” 
  &&  “ ((Zlength ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) = len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (0 <= k) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < strings_size_pre) ” 
  &&  “ (0 <= strings_size_pre) ” 
  &&  “ (strings_size_pre <= 100) ” 
  &&  “ (len = (row_len_z_28 ((Znth (i) (rows) ((@nil Z)))))) ” 
  &&  “ ((k + len ) < total) ” 
  &&  “ (0 <= len0) ” 
  &&  “ (len0 < INT_MAX) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (rows_well_formed_28 rows strings_size_pre ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p)) + 1 ) < INT_MAX)) ” 
  &&  “ (problem_28_pre_z rows ) ” 
  &&  “ (total_prefix_state_28 rows strings_size_pre total ) ” 
  &&  “ (copy_prefix_state_28 rows i k out_l ) ” 
  &&  “ (all_ascii (row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))) ) ” 
  &&  “ ((Zlength ((row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))))) = len) ”
  &&  (CharArray.undef_full (out + (k * sizeof(CHAR) ) ) len )
  **  (CharArray.full row_ptr len (row_payload_z_28 ((Znth (i) (rows) ((@nil Z))))) )
  **  (CharPtrArray2.missing_i strings_pre strings_size_pre i row_ptr rows )
  **  (((strings_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.seg row_ptr len (len + 1 ) (cons (0) ((@nil Z))) )
  **  (CharArray.full out k out_l )
  **  (CharArray.undef_seg out (k + len ) total )
.

Definition concatenate_partial_solve_wit_4 := concatenate_partial_solve_wit_4_pure -> concatenate_partial_solve_wit_4_aux.

Definition concatenate_partial_solve_wit_5 := 
forall (strings_size_pre: Z) (strings_pre: Z) (rows: (@list (@list Z))) (out_l: (@list Z)) (k: Z) (total: Z) (len0: Z) (len: Z) (out: Z) (PreH1 : ((k + 1 ) = total)) (PreH2 : (rows_well_formed_28 rows strings_size_pre )) (PreH3 : forall (p: Z) , (((0 <= p) /\ (p <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p)) + 1 ) < INT_MAX))) (PreH4 : (0 <= len0)) (PreH5 : (len0 < INT_MAX)) (PreH6 : (0 <= len)) (PreH7 : (len < INT_MAX)) (PreH8 : (problem_28_pre_z rows )) (PreH9 : (copy_prefix_state_28 rows strings_size_pre k out_l )) ,
  (CharPtrArray2.full strings_pre strings_size_pre rows )
  **  (CharArray.full out k out_l )
  **  (CharArray.undef_seg out k (k + 1 ) )
|--
  “ (0 <= k) ” 
  &&  “ ((k + 1 ) = total) ” 
  &&  “ (rows_well_formed_28 rows strings_size_pre ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p <= strings_size_pre)) -> (((concat_prefix_len_28 (rows) (p)) + 1 ) < INT_MAX)) ” 
  &&  “ (0 <= len0) ” 
  &&  “ (len0 < INT_MAX) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (problem_28_pre_z rows ) ” 
  &&  “ (copy_prefix_state_28 rows strings_size_pre k out_l ) ”
  &&  (((out + (k * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out k k (k + 1 ) )
  **  (CharPtrArray2.full strings_pre strings_size_pre rows )
  **  (CharArray.full out k out_l )
.

Module Type VC_Correct.

Include ptr_array2_Strategy_Correct.
Include char_array_Strategy_Correct.
Include string_Strategy_Correct.

Axiom proof_of_concatenate_safety_wit_1 : concatenate_safety_wit_1.
Axiom proof_of_concatenate_safety_wit_2 : concatenate_safety_wit_2.
Axiom proof_of_concatenate_safety_wit_3 : concatenate_safety_wit_3.
Axiom proof_of_concatenate_safety_wit_4 : concatenate_safety_wit_4.
Axiom proof_of_concatenate_safety_wit_5 : concatenate_safety_wit_5.
Axiom proof_of_concatenate_safety_wit_6 : concatenate_safety_wit_6.
Axiom proof_of_concatenate_safety_wit_7 : concatenate_safety_wit_7.
Axiom proof_of_concatenate_safety_wit_8 : concatenate_safety_wit_8.
Axiom proof_of_concatenate_safety_wit_9 : concatenate_safety_wit_9.
Axiom proof_of_concatenate_safety_wit_10 : concatenate_safety_wit_10.
Axiom proof_of_concatenate_safety_wit_11 : concatenate_safety_wit_11.
Axiom proof_of_concatenate_safety_wit_12 : concatenate_safety_wit_12.
Axiom proof_of_concatenate_safety_wit_13 : concatenate_safety_wit_13.
Axiom proof_of_concatenate_entail_wit_1 : concatenate_entail_wit_1.
Axiom proof_of_concatenate_entail_wit_2 : concatenate_entail_wit_2.
Axiom proof_of_concatenate_entail_wit_3 : concatenate_entail_wit_3.
Axiom proof_of_concatenate_entail_wit_4 : concatenate_entail_wit_4.
Axiom proof_of_concatenate_entail_wit_5 : concatenate_entail_wit_5.
Axiom proof_of_concatenate_entail_wit_6 : concatenate_entail_wit_6.
Axiom proof_of_concatenate_entail_wit_7 : concatenate_entail_wit_7.
Axiom proof_of_concatenate_entail_wit_8 : concatenate_entail_wit_8.
Axiom proof_of_concatenate_entail_wit_9 : concatenate_entail_wit_9.
Axiom proof_of_concatenate_entail_wit_10 : concatenate_entail_wit_10.
Axiom proof_of_concatenate_entail_wit_11 : concatenate_entail_wit_11.
Axiom proof_of_concatenate_entail_wit_12 : concatenate_entail_wit_12.
Axiom proof_of_concatenate_entail_wit_13 : concatenate_entail_wit_13.
Axiom proof_of_concatenate_entail_wit_14 : concatenate_entail_wit_14.
Axiom proof_of_concatenate_return_wit_1 : concatenate_return_wit_1.
Axiom proof_of_concatenate_partial_solve_wit_1_pure : concatenate_partial_solve_wit_1_pure.
Axiom proof_of_concatenate_partial_solve_wit_1 : concatenate_partial_solve_wit_1.
Axiom proof_of_concatenate_partial_solve_wit_2_pure : concatenate_partial_solve_wit_2_pure.
Axiom proof_of_concatenate_partial_solve_wit_2 : concatenate_partial_solve_wit_2.
Axiom proof_of_concatenate_partial_solve_wit_3_pure : concatenate_partial_solve_wit_3_pure.
Axiom proof_of_concatenate_partial_solve_wit_3 : concatenate_partial_solve_wit_3.
Axiom proof_of_concatenate_partial_solve_wit_4_pure : concatenate_partial_solve_wit_4_pure.
Axiom proof_of_concatenate_partial_solve_wit_4 : concatenate_partial_solve_wit_4.
Axiom proof_of_concatenate_partial_solve_wit_5 : concatenate_partial_solve_wit_5.

End VC_Correct.
