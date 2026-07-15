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
Require Import coins_63.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_proof.

(*----- Function fibfib -----*)

Definition fibfib_safety_wit_1 := 
forall (n_pre: Z) (n0: Z) (PreH1 : (n_pre = n0)) (PreH2 : (0 <= n0)) (PreH3 : (n0 <= 38)) (PreH4 : (problem_63_pre_z n0 )) (PreH5 : (fibfib_safe_z n0 )) ,
  ((( &( "ff" ) )) # Ptr  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (100 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 100) ”
.

Definition fibfib_safety_wit_2 := 
forall (n_pre: Z) (n0: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (n_pre = n0)) (PreH3 : (0 <= n0)) (PreH4 : (n0 <= 38)) (PreH5 : (problem_63_pre_z n0 )) (PreH6 : (fibfib_safe_z n0 )) ,
  (IntArray.undef_full retval 100 )
  **  ((( &( "ff" ) )) # Ptr  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition fibfib_safety_wit_3 := 
forall (n_pre: Z) (n0: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (n_pre = n0)) (PreH3 : (0 <= n0)) (PreH4 : (n0 <= 38)) (PreH5 : (problem_63_pre_z n0 )) (PreH6 : (fibfib_safe_z n0 )) ,
  (IntArray.undef_full retval 100 )
  **  ((( &( "ff" ) )) # Ptr  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition fibfib_safety_wit_4 := 
forall (n0: Z) (ff: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 38)) (PreH3 : (problem_63_pre_z n0 )) (PreH4 : (fibfib_safe_z n0 )) (PreH5 : (ff <> 0)) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "ff" ) )) # Ptr  |-> ff)
  **  (IntArray.seg ff 0 1 (cons (0) ((@nil Z))) )
  **  (IntArray.undef_seg ff 1 100 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition fibfib_safety_wit_5 := 
forall (n0: Z) (ff: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 38)) (PreH3 : (problem_63_pre_z n0 )) (PreH4 : (fibfib_safe_z n0 )) (PreH5 : (ff <> 0)) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "ff" ) )) # Ptr  |-> ff)
  **  (IntArray.seg ff 0 1 (cons (0) ((@nil Z))) )
  **  (IntArray.undef_seg ff 1 100 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition fibfib_safety_wit_6 := 
forall (n0: Z) (ff: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 38)) (PreH3 : (problem_63_pre_z n0 )) (PreH4 : (fibfib_safe_z n0 )) (PreH5 : (ff <> 0)) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "ff" ) )) # Ptr  |-> ff)
  **  (IntArray.seg ff 0 2 (cons (0) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg ff 2 100 )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition fibfib_safety_wit_7 := 
forall (n0: Z) (ff: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 38)) (PreH3 : (problem_63_pre_z n0 )) (PreH4 : (fibfib_safe_z n0 )) (PreH5 : (ff <> 0)) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "ff" ) )) # Ptr  |-> ff)
  **  (IntArray.seg ff 0 2 (cons (0) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg ff 2 100 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition fibfib_safety_wit_8 := 
forall (n0: Z) (ff: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 38)) (PreH3 : (problem_63_pre_z n0 )) (PreH4 : (fibfib_safe_z n0 )) (PreH5 : (ff <> 0)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "ff" ) )) # Ptr  |-> ff)
  **  (IntArray.seg ff 0 3 (fibfib_prefix_z (3)) )
  **  (IntArray.undef_seg ff 3 100 )
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition fibfib_safety_wit_9 := 
forall (n0: Z) (i: Z) (ff: Z) (PreH1 : (i <= n0)) (PreH2 : (0 <= n0)) (PreH3 : (n0 <= 38)) (PreH4 : (problem_63_pre_z n0 )) (PreH5 : (fibfib_safe_z n0 )) (PreH6 : (ff <> 0)) (PreH7 : (3 <= i)) (PreH8 : (i <= 39)) (PreH9 : (n0 < 3)) (PreH10 : (i = 3)) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "ff" ) )) # Ptr  |-> ff)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.seg ff 0 (fibfib_fill_len_z (n0) (i)) (fibfib_prefix_z ((fibfib_fill_len_z (n0) (i)))) )
  **  (IntArray.undef_seg ff (fibfib_fill_len_z (n0) (i)) 100 )
|--
  “ False ”
.

Definition fibfib_safety_wit_10 := 
forall (n0: Z) (ff: Z) (i: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 38)) (PreH3 : (problem_63_pre_z n0 )) (PreH4 : (fibfib_safe_z n0 )) (PreH5 : (ff <> 0)) (PreH6 : (3 <= i)) (PreH7 : (i <= n0)) (PreH8 : ((fibfib_fill_len_z (n0) (i)) = i)) ,
  ((( &( "a" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "ff" ) )) # Ptr  |-> ff)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.seg ff 0 i (fibfib_prefix_z (i)) )
  **  (IntArray.undef_seg ff i 100 )
|--
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition fibfib_safety_wit_11 := 
forall (n0: Z) (ff: Z) (i: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 38)) (PreH3 : (problem_63_pre_z n0 )) (PreH4 : (fibfib_safe_z n0 )) (PreH5 : (ff <> 0)) (PreH6 : (3 <= i)) (PreH7 : (i <= n0)) (PreH8 : ((fibfib_fill_len_z (n0) (i)) = i)) ,
  ((( &( "a" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "ff" ) )) # Ptr  |-> ff)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.seg ff 0 i (fibfib_prefix_z (i)) )
  **  (IntArray.undef_seg ff i 100 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition fibfib_safety_wit_12 := 
forall (n0: Z) (ff: Z) (i: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 38)) (PreH3 : (problem_63_pre_z n0 )) (PreH4 : (fibfib_safe_z n0 )) (PreH5 : (ff <> 0)) (PreH6 : (3 <= i)) (PreH7 : (i <= n0)) (PreH8 : ((fibfib_fill_len_z (n0) (i)) = i)) ,
  ((( &( "b" ) )) # Int  |->_)
  **  (IntArray.seg ff 0 i (fibfib_prefix_z (i)) )
  **  ((( &( "a" ) )) # Int  |-> (Znth ((i - 1 ) - 0 ) (fibfib_prefix_z (i)) 0))
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "ff" ) )) # Ptr  |-> ff)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_seg ff i 100 )
|--
  “ ((i - 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 2 )) ”
.

Definition fibfib_safety_wit_13 := 
forall (n0: Z) (ff: Z) (i: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 38)) (PreH3 : (problem_63_pre_z n0 )) (PreH4 : (fibfib_safe_z n0 )) (PreH5 : (ff <> 0)) (PreH6 : (3 <= i)) (PreH7 : (i <= n0)) (PreH8 : ((fibfib_fill_len_z (n0) (i)) = i)) ,
  ((( &( "b" ) )) # Int  |->_)
  **  (IntArray.seg ff 0 i (fibfib_prefix_z (i)) )
  **  ((( &( "a" ) )) # Int  |-> (Znth ((i - 1 ) - 0 ) (fibfib_prefix_z (i)) 0))
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "ff" ) )) # Ptr  |-> ff)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_seg ff i 100 )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition fibfib_safety_wit_14 := 
forall (n0: Z) (ff: Z) (i: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 38)) (PreH3 : (problem_63_pre_z n0 )) (PreH4 : (fibfib_safe_z n0 )) (PreH5 : (ff <> 0)) (PreH6 : (3 <= i)) (PreH7 : (i <= n0)) (PreH8 : ((fibfib_fill_len_z (n0) (i)) = i)) ,
  ((( &( "c" ) )) # Int  |->_)
  **  (IntArray.seg ff 0 i (fibfib_prefix_z (i)) )
  **  ((( &( "b" ) )) # Int  |-> (Znth ((i - 2 ) - 0 ) (fibfib_prefix_z (i)) 0))
  **  ((( &( "a" ) )) # Int  |-> (Znth ((i - 1 ) - 0 ) (fibfib_prefix_z (i)) 0))
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "ff" ) )) # Ptr  |-> ff)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_seg ff i 100 )
|--
  “ ((i - 3 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 3 )) ”
.

Definition fibfib_safety_wit_15 := 
forall (n0: Z) (ff: Z) (i: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 38)) (PreH3 : (problem_63_pre_z n0 )) (PreH4 : (fibfib_safe_z n0 )) (PreH5 : (ff <> 0)) (PreH6 : (3 <= i)) (PreH7 : (i <= n0)) (PreH8 : ((fibfib_fill_len_z (n0) (i)) = i)) ,
  ((( &( "c" ) )) # Int  |->_)
  **  (IntArray.seg ff 0 i (fibfib_prefix_z (i)) )
  **  ((( &( "b" ) )) # Int  |-> (Znth ((i - 2 ) - 0 ) (fibfib_prefix_z (i)) 0))
  **  ((( &( "a" ) )) # Int  |-> (Znth ((i - 1 ) - 0 ) (fibfib_prefix_z (i)) 0))
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "ff" ) )) # Ptr  |-> ff)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_seg ff i 100 )
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition fibfib_safety_wit_16 := 
(
forall (n0: Z) (ff: Z) (i: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 38)) (PreH3 : (problem_63_pre_z n0 )) (PreH4 : (fibfib_safe_z n0 )) (PreH5 : (ff <> 0)) (PreH6 : (3 <= i)) (PreH7 : (i <= n0)) (PreH8 : ((fibfib_fill_len_z (n0) (i)) = i)) ,
  (IntArray.seg ff 0 i (fibfib_prefix_z (i)) )
  **  ((( &( "c" ) )) # Int  |-> (Znth ((i - 3 ) - 0 ) (fibfib_prefix_z (i)) 0))
  **  ((( &( "b" ) )) # Int  |-> (Znth ((i - 2 ) - 0 ) (fibfib_prefix_z (i)) 0))
  **  ((( &( "a" ) )) # Int  |-> (Znth ((i - 1 ) - 0 ) (fibfib_prefix_z (i)) 0))
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "ff" ) )) # Ptr  |-> ff)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_seg ff i 100 )
|--
  “ ((((Znth ((i - 1 ) - 0 ) (fibfib_prefix_z (i)) 0) + (Znth ((i - 2 ) - 0 ) (fibfib_prefix_z (i)) 0) ) + (Znth ((i - 3 ) - 0 ) (fibfib_prefix_z (i)) 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((Znth ((i - 1 ) - 0 ) (fibfib_prefix_z (i)) 0) + (Znth ((i - 2 ) - 0 ) (fibfib_prefix_z (i)) 0) ) + (Znth ((i - 3 ) - 0 ) (fibfib_prefix_z (i)) 0) )) ”
) \/
(
forall (n0: Z) (ff: Z) (i: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 38)) (PreH3 : (problem_63_pre_z n0 )) (PreH4 : (fibfib_safe_z n0 )) (PreH5 : (ff <> 0)) (PreH6 : (3 <= i)) (PreH7 : (i <= n0)) (PreH8 : ((fibfib_fill_len_z (n0) (i)) = i)) ,
  (IntArray.seg ff 0 i (fibfib_prefix_z (i)) )
  **  ((( &( "c" ) )) # Int  |-> (Znth ((i - 3 ) - 0 ) (fibfib_prefix_z (i)) 0))
  **  ((( &( "b" ) )) # Int  |-> (Znth ((i - 2 ) - 0 ) (fibfib_prefix_z (i)) 0))
  **  ((( &( "a" ) )) # Int  |-> (Znth ((i - 1 ) - 0 ) (fibfib_prefix_z (i)) 0))
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "ff" ) )) # Ptr  |-> ff)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_seg ff i 100 )
|--
  “ ((((Znth ((i - 1 ) - 0 ) (fibfib_prefix_z (i)) 0) + (Znth ((i - 2 ) - 0 ) (fibfib_prefix_z (i)) 0) ) + (Znth ((i - 3 ) - 0 ) (fibfib_prefix_z (i)) 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((Znth ((i - 1 ) - 0 ) (fibfib_prefix_z (i)) 0) + (Znth ((i - 2 ) - 0 ) (fibfib_prefix_z (i)) 0) ) + (Znth ((i - 3 ) - 0 ) (fibfib_prefix_z (i)) 0) )) ”
).

Definition fibfib_safety_wit_16_split_goal_1 := 
forall (n0: Z) (ff: Z) (i: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 38)) (PreH3 : (problem_63_pre_z n0 )) (PreH4 : (fibfib_safe_z n0 )) (PreH5 : (ff <> 0)) (PreH6 : (3 <= i)) (PreH7 : (i <= n0)) (PreH8 : ((fibfib_fill_len_z (n0) (i)) = i)) ,
  (IntArray.seg ff 0 i (fibfib_prefix_z (i)) )
  **  ((( &( "c" ) )) # Int  |-> (Znth ((i - 3 ) - 0 ) (fibfib_prefix_z (i)) 0))
  **  ((( &( "b" ) )) # Int  |-> (Znth ((i - 2 ) - 0 ) (fibfib_prefix_z (i)) 0))
  **  ((( &( "a" ) )) # Int  |-> (Znth ((i - 1 ) - 0 ) (fibfib_prefix_z (i)) 0))
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "ff" ) )) # Ptr  |-> ff)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_seg ff i 100 )
|--
  “ ((((Znth ((i - 1 ) - 0 ) (fibfib_prefix_z (i)) 0) + (Znth ((i - 2 ) - 0 ) (fibfib_prefix_z (i)) 0) ) + (Znth ((i - 3 ) - 0 ) (fibfib_prefix_z (i)) 0) ) <= INT_MAX) ”
.

Definition fibfib_safety_wit_16_split_goal_2 := 
forall (n0: Z) (ff: Z) (i: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 38)) (PreH3 : (problem_63_pre_z n0 )) (PreH4 : (fibfib_safe_z n0 )) (PreH5 : (ff <> 0)) (PreH6 : (3 <= i)) (PreH7 : (i <= n0)) (PreH8 : ((fibfib_fill_len_z (n0) (i)) = i)) ,
  (IntArray.seg ff 0 i (fibfib_prefix_z (i)) )
  **  ((( &( "c" ) )) # Int  |-> (Znth ((i - 3 ) - 0 ) (fibfib_prefix_z (i)) 0))
  **  ((( &( "b" ) )) # Int  |-> (Znth ((i - 2 ) - 0 ) (fibfib_prefix_z (i)) 0))
  **  ((( &( "a" ) )) # Int  |-> (Znth ((i - 1 ) - 0 ) (fibfib_prefix_z (i)) 0))
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "ff" ) )) # Ptr  |-> ff)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_seg ff i 100 )
|--
  “ ((INT_MIN) <= (((Znth ((i - 1 ) - 0 ) (fibfib_prefix_z (i)) 0) + (Znth ((i - 2 ) - 0 ) (fibfib_prefix_z (i)) 0) ) + (Znth ((i - 3 ) - 0 ) (fibfib_prefix_z (i)) 0) )) ”
.

Definition fibfib_safety_wit_17 := 
(
forall (n0: Z) (ff: Z) (i: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 38)) (PreH3 : (problem_63_pre_z n0 )) (PreH4 : (fibfib_safe_z n0 )) (PreH5 : (ff <> 0)) (PreH6 : (3 <= i)) (PreH7 : (i <= n0)) (PreH8 : ((fibfib_fill_len_z (n0) (i)) = i)) ,
  (IntArray.seg ff 0 i (fibfib_prefix_z (i)) )
  **  ((( &( "c" ) )) # Int  |-> (Znth ((i - 3 ) - 0 ) (fibfib_prefix_z (i)) 0))
  **  ((( &( "b" ) )) # Int  |-> (Znth ((i - 2 ) - 0 ) (fibfib_prefix_z (i)) 0))
  **  ((( &( "a" ) )) # Int  |-> (Znth ((i - 1 ) - 0 ) (fibfib_prefix_z (i)) 0))
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "ff" ) )) # Ptr  |-> ff)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_seg ff i 100 )
|--
  “ (((Znth ((i - 1 ) - 0 ) (fibfib_prefix_z (i)) 0) + (Znth ((i - 2 ) - 0 ) (fibfib_prefix_z (i)) 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth ((i - 1 ) - 0 ) (fibfib_prefix_z (i)) 0) + (Znth ((i - 2 ) - 0 ) (fibfib_prefix_z (i)) 0) )) ”
) \/
(
forall (n0: Z) (ff: Z) (i: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 38)) (PreH3 : (problem_63_pre_z n0 )) (PreH4 : (fibfib_safe_z n0 )) (PreH5 : (ff <> 0)) (PreH6 : (3 <= i)) (PreH7 : (i <= n0)) (PreH8 : ((fibfib_fill_len_z (n0) (i)) = i)) ,
  (IntArray.seg ff 0 i (fibfib_prefix_z (i)) )
  **  ((( &( "c" ) )) # Int  |-> (Znth ((i - 3 ) - 0 ) (fibfib_prefix_z (i)) 0))
  **  ((( &( "b" ) )) # Int  |-> (Znth ((i - 2 ) - 0 ) (fibfib_prefix_z (i)) 0))
  **  ((( &( "a" ) )) # Int  |-> (Znth ((i - 1 ) - 0 ) (fibfib_prefix_z (i)) 0))
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "ff" ) )) # Ptr  |-> ff)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_seg ff i 100 )
|--
  “ (((Znth ((i - 1 ) - 0 ) (fibfib_prefix_z (i)) 0) + (Znth ((i - 2 ) - 0 ) (fibfib_prefix_z (i)) 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth ((i - 1 ) - 0 ) (fibfib_prefix_z (i)) 0) + (Znth ((i - 2 ) - 0 ) (fibfib_prefix_z (i)) 0) )) ”
).

Definition fibfib_safety_wit_17_split_goal_1 := 
forall (n0: Z) (ff: Z) (i: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 38)) (PreH3 : (problem_63_pre_z n0 )) (PreH4 : (fibfib_safe_z n0 )) (PreH5 : (ff <> 0)) (PreH6 : (3 <= i)) (PreH7 : (i <= n0)) (PreH8 : ((fibfib_fill_len_z (n0) (i)) = i)) ,
  (IntArray.seg ff 0 i (fibfib_prefix_z (i)) )
  **  ((( &( "c" ) )) # Int  |-> (Znth ((i - 3 ) - 0 ) (fibfib_prefix_z (i)) 0))
  **  ((( &( "b" ) )) # Int  |-> (Znth ((i - 2 ) - 0 ) (fibfib_prefix_z (i)) 0))
  **  ((( &( "a" ) )) # Int  |-> (Znth ((i - 1 ) - 0 ) (fibfib_prefix_z (i)) 0))
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "ff" ) )) # Ptr  |-> ff)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_seg ff i 100 )
|--
  “ (((Znth ((i - 1 ) - 0 ) (fibfib_prefix_z (i)) 0) + (Znth ((i - 2 ) - 0 ) (fibfib_prefix_z (i)) 0) ) <= INT_MAX) ”
.

Definition fibfib_safety_wit_17_split_goal_2 := 
forall (n0: Z) (ff: Z) (i: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 38)) (PreH3 : (problem_63_pre_z n0 )) (PreH4 : (fibfib_safe_z n0 )) (PreH5 : (ff <> 0)) (PreH6 : (3 <= i)) (PreH7 : (i <= n0)) (PreH8 : ((fibfib_fill_len_z (n0) (i)) = i)) ,
  (IntArray.seg ff 0 i (fibfib_prefix_z (i)) )
  **  ((( &( "c" ) )) # Int  |-> (Znth ((i - 3 ) - 0 ) (fibfib_prefix_z (i)) 0))
  **  ((( &( "b" ) )) # Int  |-> (Znth ((i - 2 ) - 0 ) (fibfib_prefix_z (i)) 0))
  **  ((( &( "a" ) )) # Int  |-> (Znth ((i - 1 ) - 0 ) (fibfib_prefix_z (i)) 0))
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "ff" ) )) # Ptr  |-> ff)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_seg ff i 100 )
|--
  “ ((INT_MIN) <= ((Znth ((i - 1 ) - 0 ) (fibfib_prefix_z (i)) 0) + (Znth ((i - 2 ) - 0 ) (fibfib_prefix_z (i)) 0) )) ”
.

Definition fibfib_safety_wit_18 := 
forall (n0: Z) (ff: Z) (i: Z) (a: Z) (b: Z) (c: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 38)) (PreH3 : (problem_63_pre_z n0 )) (PreH4 : (fibfib_safe_z n0 )) (PreH5 : (ff <> 0)) (PreH6 : (3 <= i)) (PreH7 : (i <= n0)) (PreH8 : (a = (fibfib_z ((i - 1 ))))) (PreH9 : (b = (fibfib_z ((i - 2 ))))) (PreH10 : (c = (fibfib_z ((i - 3 ))))) (PreH11 : (0 <= (a + b ))) (PreH12 : ((a + b ) <= INT_MAX)) (PreH13 : ((fibfib_z (i)) = ((a + b ) + c ))) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "ff" ) )) # Ptr  |-> ff)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.seg ff 0 (i + 1 ) (fibfib_prefix_z ((i + 1 ))) )
  **  (IntArray.undef_seg ff (i + 1 ) 100 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition fibfib_safety_wit_19 := 
forall (n0: Z) (ff: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 38)) (PreH3 : (problem_63_pre_z n0 )) (PreH4 : (fibfib_safe_z n0 )) (PreH5 : (ff <> 0)) ,
  ((( &( "filled" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "ff" ) )) # Ptr  |-> ff)
  **  (IntArray.seg ff 0 (fibfib_fill_len_z (n0) ((n0 + 1 ))) (fibfib_prefix_z ((fibfib_fill_len_z (n0) ((n0 + 1 ))))) )
  **  (IntArray.undef_seg ff (fibfib_fill_len_z (n0) ((n0 + 1 ))) 100 )
|--
  “ ((n0 + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n0 + 1 )) ”
.

Definition fibfib_safety_wit_20 := 
forall (n0: Z) (ff: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 38)) (PreH3 : (problem_63_pre_z n0 )) (PreH4 : (fibfib_safe_z n0 )) (PreH5 : (ff <> 0)) ,
  ((( &( "filled" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "ff" ) )) # Ptr  |-> ff)
  **  (IntArray.seg ff 0 (fibfib_fill_len_z (n0) ((n0 + 1 ))) (fibfib_prefix_z ((fibfib_fill_len_z (n0) ((n0 + 1 ))))) )
  **  (IntArray.undef_seg ff (fibfib_fill_len_z (n0) ((n0 + 1 ))) 100 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition fibfib_safety_wit_21 := 
forall (n0: Z) (ff: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 38)) (PreH3 : (problem_63_pre_z n0 )) (PreH4 : (fibfib_safe_z n0 )) (PreH5 : (ff <> 0)) ,
  ((( &( "filled" ) )) # Int  |-> (n0 + 1 ))
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "ff" ) )) # Ptr  |-> ff)
  **  (IntArray.seg ff 0 (fibfib_fill_len_z (n0) ((n0 + 1 ))) (fibfib_prefix_z ((fibfib_fill_len_z (n0) ((n0 + 1 ))))) )
  **  (IntArray.undef_seg ff (fibfib_fill_len_z (n0) ((n0 + 1 ))) 100 )
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition fibfib_safety_wit_22 := 
forall (n0: Z) (ff: Z) (PreH1 : (n0 < 3)) (PreH2 : (0 <= n0)) (PreH3 : (n0 <= 38)) (PreH4 : (problem_63_pre_z n0 )) (PreH5 : (fibfib_safe_z n0 )) (PreH6 : (ff <> 0)) ,
  ((( &( "filled" ) )) # Int  |-> (n0 + 1 ))
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "ff" ) )) # Ptr  |-> ff)
  **  (IntArray.seg ff 0 (fibfib_fill_len_z (n0) ((n0 + 1 ))) (fibfib_prefix_z ((fibfib_fill_len_z (n0) ((n0 + 1 ))))) )
  **  (IntArray.undef_seg ff (fibfib_fill_len_z (n0) ((n0 + 1 ))) 100 )
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition fibfib_safety_wit_23 := 
forall (n0: Z) (result: Z) (filled: Z) (ff: Z) (PreH1 : (result = (fibfib_z (n0)))) (PreH2 : (filled = (fibfib_fill_len_z (n0) ((n0 + 1 ))))) (PreH3 : (n0 < filled)) (PreH4 : (0 <= n0)) (PreH5 : (n0 <= 38)) (PreH6 : (problem_63_pre_z n0 )) (PreH7 : (fibfib_safe_z n0 )) (PreH8 : (ff <> 0)) (PreH9 : (filled <= 100)) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "result" ) )) # Int  |-> result)
  **  ((( &( "filled" ) )) # Int  |-> filled)
  **  ((( &( "ff" ) )) # Ptr  |-> ff)
  **  (IntArray.seg ff 0 filled (fibfib_prefix_z (filled)) )
  **  (IntArray.undef_seg ff filled 100 )
|--
  “ (100 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 100) ”
.

Definition fibfib_entail_wit_1 := 
(
forall (n_pre: Z) (n0: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (n_pre = n0)) (PreH3 : (0 <= n0)) (PreH4 : (n0 <= 38)) (PreH5 : (problem_63_pre_z n0 )) (PreH6 : (fibfib_safe_z n0 )) ,
  (((retval + (0 * sizeof(INT) ) )) # Int  |-> 0)
  **  (IntArray.undef_seg retval 1 100 )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (0 <= n0) ” 
  &&  “ (n0 <= 38) ” 
  &&  “ (problem_63_pre_z n0 ) ” 
  &&  “ (fibfib_safe_z n0 ) ” 
  &&  “ (retval <> 0) ”
  &&  ((( &( "n" ) )) # Int  |-> n0)
  **  (IntArray.seg retval 0 1 (cons (0) ((@nil Z))) )
  **  (IntArray.undef_seg retval 1 100 )
) \/
(
forall (n_pre: Z) (n0: Z) (retval: Z) (PreH1 : (0 <= INT_MAX)) (PreH2 : (0 >= INT_MIN)) (PreH3 : (retval <> 0)) (PreH4 : (n_pre = n0)) (PreH5 : (0 <= n0)) (PreH6 : (n0 <= 38)) (PreH7 : (problem_63_pre_z n0 )) (PreH8 : (fibfib_safe_z n0 )) ,
  (((retval + (0 * sizeof(INT) ) )) # Int  |-> 0)
|--
  (IntArray.seg retval 0 1 (cons (0) ((@nil Z))) )
).

Definition fibfib_entail_wit_1_split_goal_spatial := 
forall (n_pre: Z) (n0: Z) (retval: Z) (PreH1 : (0 <= INT_MAX)) (PreH2 : (0 >= INT_MIN)) (PreH3 : (retval <> 0)) (PreH4 : (n_pre = n0)) (PreH5 : (0 <= n0)) (PreH6 : (n0 <= 38)) (PreH7 : (problem_63_pre_z n0 )) (PreH8 : (fibfib_safe_z n0 )) ,
  (((retval + (0 * sizeof(INT) ) )) # Int  |-> 0)
|--
  (IntArray.seg retval 0 1 (cons (0) ((@nil Z))) )
.

Definition fibfib_entail_wit_2 := 
(
forall (n0: Z) (ff: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 38)) (PreH3 : (problem_63_pre_z n0 )) (PreH4 : (fibfib_safe_z n0 )) (PreH5 : (ff <> 0)) ,
  (IntArray.seg ff 0 (1 + 1 ) (app ((cons (0) ((@nil Z)))) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg ff (1 + 1 ) 100 )
|--
  “ (0 <= n0) ” 
  &&  “ (n0 <= 38) ” 
  &&  “ (problem_63_pre_z n0 ) ” 
  &&  “ (fibfib_safe_z n0 ) ” 
  &&  “ (ff <> 0) ”
  &&  (IntArray.seg ff 0 2 (cons (0) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg ff 2 100 )
) \/
(
forall (n0: Z) (ff: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 38)) (PreH3 : (problem_63_pre_z n0 )) (PreH4 : (fibfib_safe_z n0 )) (PreH5 : (ff <> 0)) ,
  (IntArray.seg ff 0 (1 + 1 ) (app ((cons (0) ((@nil Z)))) ((cons (0) ((@nil Z))))) )
|--
  (IntArray.seg ff 0 2 (cons (0) ((cons (0) ((@nil Z))))) )
).

Definition fibfib_entail_wit_2_split_goal_spatial := 
forall (n0: Z) (ff: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 38)) (PreH3 : (problem_63_pre_z n0 )) (PreH4 : (fibfib_safe_z n0 )) (PreH5 : (ff <> 0)) ,
  (IntArray.seg ff 0 (1 + 1 ) (app ((cons (0) ((@nil Z)))) ((cons (0) ((@nil Z))))) )
|--
  (IntArray.seg ff 0 2 (cons (0) ((cons (0) ((@nil Z))))) )
.

Definition fibfib_entail_wit_3 := 
(
forall (n0: Z) (ff: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 38)) (PreH3 : (problem_63_pre_z n0 )) (PreH4 : (fibfib_safe_z n0 )) (PreH5 : (ff <> 0)) ,
  (IntArray.seg ff 0 (2 + 1 ) (app ((cons (0) ((cons (0) ((@nil Z)))))) ((cons (1) ((@nil Z))))) )
  **  (IntArray.undef_seg ff (2 + 1 ) 100 )
|--
  “ (0 <= n0) ” 
  &&  “ (n0 <= 38) ” 
  &&  “ (problem_63_pre_z n0 ) ” 
  &&  “ (fibfib_safe_z n0 ) ” 
  &&  “ (ff <> 0) ”
  &&  (IntArray.seg ff 0 3 (fibfib_prefix_z (3)) )
  **  (IntArray.undef_seg ff 3 100 )
) \/
(
forall (n0: Z) (ff: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 38)) (PreH3 : (problem_63_pre_z n0 )) (PreH4 : (fibfib_safe_z n0 )) (PreH5 : (ff <> 0)) ,
  (IntArray.seg ff 0 (2 + 1 ) (app ((cons (0) ((cons (0) ((@nil Z)))))) ((cons (1) ((@nil Z))))) )
|--
  (IntArray.seg ff 0 3 (fibfib_prefix_z (3)) )
).

Definition fibfib_entail_wit_3_split_goal_spatial := 
forall (n0: Z) (ff: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 38)) (PreH3 : (problem_63_pre_z n0 )) (PreH4 : (fibfib_safe_z n0 )) (PreH5 : (ff <> 0)) ,
  (IntArray.seg ff 0 (2 + 1 ) (app ((cons (0) ((cons (0) ((@nil Z)))))) ((cons (1) ((@nil Z))))) )
|--
  (IntArray.seg ff 0 3 (fibfib_prefix_z (3)) )
.

Definition fibfib_entail_wit_4 := 
forall (n0: Z) (ff: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 38)) (PreH3 : (problem_63_pre_z n0 )) (PreH4 : (fibfib_safe_z n0 )) (PreH5 : (ff <> 0)) ,
  (IntArray.seg ff 0 3 (fibfib_prefix_z (3)) )
  **  (IntArray.undef_seg ff 3 100 )
|--
  (“ (0 <= n0) ” 
  &&  “ (n0 <= 38) ” 
  &&  “ (problem_63_pre_z n0 ) ” 
  &&  “ (fibfib_safe_z n0 ) ” 
  &&  “ (ff <> 0) ” 
  &&  “ (3 <= 3) ” 
  &&  “ (3 <= 39) ” 
  &&  “ (n0 < 3) ” 
  &&  “ (3 = 3) ”
  &&  (IntArray.seg ff 0 (fibfib_fill_len_z (n0) (3)) (fibfib_prefix_z ((fibfib_fill_len_z (n0) (3)))) )
  **  (IntArray.undef_seg ff (fibfib_fill_len_z (n0) (3)) 100 ))
  ||
  (“ (0 <= n0) ” 
  &&  “ (n0 <= 38) ” 
  &&  “ (problem_63_pre_z n0 ) ” 
  &&  “ (fibfib_safe_z n0 ) ” 
  &&  “ (ff <> 0) ” 
  &&  “ (3 <= 3) ” 
  &&  “ (3 <= 39) ” 
  &&  “ (3 <= n0) ” 
  &&  “ (3 <= (n0 + 1 )) ”
  &&  (IntArray.seg ff 0 (fibfib_fill_len_z (n0) (3)) (fibfib_prefix_z ((fibfib_fill_len_z (n0) (3)))) )
  **  (IntArray.undef_seg ff (fibfib_fill_len_z (n0) (3)) 100 ))
.

Definition fibfib_entail_wit_5 := 
(
forall (n0: Z) (i: Z) (ff: Z) (PreH1 : (i <= n0)) (PreH2 : (0 <= n0)) (PreH3 : (n0 <= 38)) (PreH4 : (problem_63_pre_z n0 )) (PreH5 : (fibfib_safe_z n0 )) (PreH6 : (ff <> 0)) (PreH7 : (3 <= i)) (PreH8 : (i <= 39)) (PreH9 : (3 <= n0)) (PreH10 : (i <= (n0 + 1 ))) ,
  (IntArray.seg ff 0 (fibfib_fill_len_z (n0) (i)) (fibfib_prefix_z ((fibfib_fill_len_z (n0) (i)))) )
  **  (IntArray.undef_seg ff (fibfib_fill_len_z (n0) (i)) 100 )
|--
  “ (0 <= n0) ” 
  &&  “ (n0 <= 38) ” 
  &&  “ (problem_63_pre_z n0 ) ” 
  &&  “ (fibfib_safe_z n0 ) ” 
  &&  “ (ff <> 0) ” 
  &&  “ (3 <= i) ” 
  &&  “ (i <= n0) ” 
  &&  “ ((fibfib_fill_len_z (n0) (i)) = i) ”
  &&  (IntArray.seg ff 0 i (fibfib_prefix_z (i)) )
  **  (IntArray.undef_seg ff i 100 )
) \/
(
forall (n0: Z) (i: Z) (ff: Z) (PreH1 : (i <= n0)) (PreH2 : (0 <= n0)) (PreH3 : (n0 <= 38)) (PreH4 : (problem_63_pre_z n0 )) (PreH5 : (fibfib_safe_z n0 )) (PreH6 : (ff <> 0)) (PreH7 : (3 <= i)) (PreH8 : (i <= 39)) (PreH9 : (3 <= n0)) (PreH10 : (i <= (n0 + 1 ))) ,
  (IntArray.seg ff 0 (fibfib_fill_len_z (n0) (i)) (fibfib_prefix_z ((fibfib_fill_len_z (n0) (i)))) )
  **  (IntArray.undef_seg ff (fibfib_fill_len_z (n0) (i)) 100 )
|--
  “ ((fibfib_fill_len_z (n0) (i)) = i) ”
  &&  (IntArray.seg ff 0 i (fibfib_prefix_z (i)) )
  **  (IntArray.undef_seg ff i 100 )
).

Definition fibfib_entail_wit_5_split_goal_1 := 
forall (n0: Z) (i: Z) (ff: Z) (PreH1 : (i <= n0)) (PreH2 : (0 <= n0)) (PreH3 : (n0 <= 38)) (PreH4 : (problem_63_pre_z n0 )) (PreH5 : (fibfib_safe_z n0 )) (PreH6 : (ff <> 0)) (PreH7 : (3 <= i)) (PreH8 : (i <= 39)) (PreH9 : (3 <= n0)) (PreH10 : (i <= (n0 + 1 ))) ,
  (IntArray.seg ff 0 (fibfib_fill_len_z (n0) (i)) (fibfib_prefix_z ((fibfib_fill_len_z (n0) (i)))) )
  **  (IntArray.undef_seg ff (fibfib_fill_len_z (n0) (i)) 100 )
|--
  “ ((fibfib_fill_len_z (n0) (i)) = i) ”
.

Definition fibfib_entail_wit_5_split_goal_spatial := 
forall (n0: Z) (i: Z) (ff: Z) (PreH1 : (i <= n0)) (PreH2 : (0 <= n0)) (PreH3 : (n0 <= 38)) (PreH4 : (problem_63_pre_z n0 )) (PreH5 : (fibfib_safe_z n0 )) (PreH6 : (ff <> 0)) (PreH7 : (3 <= i)) (PreH8 : (i <= 39)) (PreH9 : (3 <= n0)) (PreH10 : (i <= (n0 + 1 ))) ,
  (IntArray.seg ff 0 (fibfib_fill_len_z (n0) (i)) (fibfib_prefix_z ((fibfib_fill_len_z (n0) (i)))) )
  **  (IntArray.undef_seg ff (fibfib_fill_len_z (n0) (i)) 100 )
|--
  (IntArray.seg ff 0 i (fibfib_prefix_z (i)) )
  **  (IntArray.undef_seg ff i 100 )
.

Definition fibfib_entail_wit_6 := 
(
forall (n0: Z) (ff: Z) (i: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 38)) (PreH3 : (problem_63_pre_z n0 )) (PreH4 : (fibfib_safe_z n0 )) (PreH5 : (ff <> 0)) (PreH6 : (3 <= i)) (PreH7 : (i <= n0)) (PreH8 : ((fibfib_fill_len_z (n0) (i)) = i)) ,
  (IntArray.seg ff 0 (i + 1 ) (app ((fibfib_prefix_z (i))) ((cons ((((Znth ((i - 1 ) - 0 ) (fibfib_prefix_z (i)) 0) + (Znth ((i - 2 ) - 0 ) (fibfib_prefix_z (i)) 0) ) + (Znth ((i - 3 ) - 0 ) (fibfib_prefix_z (i)) 0) )) ((@nil Z))))) )
  **  (IntArray.undef_seg ff (i + 1 ) 100 )
|--
  “ (0 <= n0) ” 
  &&  “ (n0 <= 38) ” 
  &&  “ (problem_63_pre_z n0 ) ” 
  &&  “ (fibfib_safe_z n0 ) ” 
  &&  “ (ff <> 0) ” 
  &&  “ (3 <= i) ” 
  &&  “ (i <= n0) ” 
  &&  “ ((Znth ((i - 1 ) - 0 ) (fibfib_prefix_z (i)) 0) = (fibfib_z ((i - 1 )))) ” 
  &&  “ ((Znth ((i - 2 ) - 0 ) (fibfib_prefix_z (i)) 0) = (fibfib_z ((i - 2 )))) ” 
  &&  “ ((Znth ((i - 3 ) - 0 ) (fibfib_prefix_z (i)) 0) = (fibfib_z ((i - 3 )))) ” 
  &&  “ (0 <= ((Znth ((i - 1 ) - 0 ) (fibfib_prefix_z (i)) 0) + (Znth ((i - 2 ) - 0 ) (fibfib_prefix_z (i)) 0) )) ” 
  &&  “ (((Znth ((i - 1 ) - 0 ) (fibfib_prefix_z (i)) 0) + (Znth ((i - 2 ) - 0 ) (fibfib_prefix_z (i)) 0) ) <= INT_MAX) ” 
  &&  “ ((fibfib_z (i)) = (((Znth ((i - 1 ) - 0 ) (fibfib_prefix_z (i)) 0) + (Znth ((i - 2 ) - 0 ) (fibfib_prefix_z (i)) 0) ) + (Znth ((i - 3 ) - 0 ) (fibfib_prefix_z (i)) 0) )) ”
  &&  (IntArray.seg ff 0 (i + 1 ) (fibfib_prefix_z ((i + 1 ))) )
  **  (IntArray.undef_seg ff (i + 1 ) 100 )
) \/
(
forall (n0: Z) (ff: Z) (i: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 38)) (PreH3 : (problem_63_pre_z n0 )) (PreH4 : (fibfib_safe_z n0 )) (PreH5 : (ff <> 0)) (PreH6 : (3 <= i)) (PreH7 : (i <= n0)) (PreH8 : ((fibfib_fill_len_z (n0) (i)) = i)) ,
  TT && emp 
|--
  “ ((fibfib_z (i)) = (((Znth ((i - 1 ) - 0 ) (fibfib_prefix_z (i)) 0) + (Znth ((i - 2 ) - 0 ) (fibfib_prefix_z (i)) 0) ) + (Znth ((i - 3 ) - 0 ) (fibfib_prefix_z (i)) 0) )) ” 
  &&  “ (((Znth ((i - 1 ) - 0 ) (fibfib_prefix_z (i)) 0) + (Znth ((i - 2 ) - 0 ) (fibfib_prefix_z (i)) 0) ) <= INT_MAX) ” 
  &&  “ (0 <= ((Znth ((i - 1 ) - 0 ) (fibfib_prefix_z (i)) 0) + (Znth ((i - 2 ) - 0 ) (fibfib_prefix_z (i)) 0) )) ” 
  &&  “ ((Znth ((i - 3 ) - 0 ) (fibfib_prefix_z (i)) 0) = (fibfib_z ((i - 3 )))) ” 
  &&  “ ((Znth ((i - 2 ) - 0 ) (fibfib_prefix_z (i)) 0) = (fibfib_z ((i - 2 )))) ” 
  &&  “ ((Znth ((i - 1 ) - 0 ) (fibfib_prefix_z (i)) 0) = (fibfib_z ((i - 1 )))) ” 
  &&  “ ((app ((fibfib_prefix_z (i))) ((cons ((((Znth ((i - 1 ) - 0 ) (fibfib_prefix_z (i)) 0) + (Znth ((i - 2 ) - 0 ) (fibfib_prefix_z (i)) 0) ) + (Znth ((i - 3 ) - 0 ) (fibfib_prefix_z (i)) 0) )) ((@nil Z))))) = (fibfib_prefix_z ((i + 1 )))) ”
  &&  emp
).

Definition fibfib_entail_wit_6_split_goal_1 := 
forall (n0: Z) (ff: Z) (i: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 38)) (PreH3 : (problem_63_pre_z n0 )) (PreH4 : (fibfib_safe_z n0 )) (PreH5 : (ff <> 0)) (PreH6 : (3 <= i)) (PreH7 : (i <= n0)) (PreH8 : ((fibfib_fill_len_z (n0) (i)) = i)) ,
  TT && emp 
|--
  “ ((fibfib_z (i)) = (((Znth ((i - 1 ) - 0 ) (fibfib_prefix_z (i)) 0) + (Znth ((i - 2 ) - 0 ) (fibfib_prefix_z (i)) 0) ) + (Znth ((i - 3 ) - 0 ) (fibfib_prefix_z (i)) 0) )) ”
.

Definition fibfib_entail_wit_6_split_goal_2 := 
forall (n0: Z) (ff: Z) (i: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 38)) (PreH3 : (problem_63_pre_z n0 )) (PreH4 : (fibfib_safe_z n0 )) (PreH5 : (ff <> 0)) (PreH6 : (3 <= i)) (PreH7 : (i <= n0)) (PreH8 : ((fibfib_fill_len_z (n0) (i)) = i)) ,
  TT && emp 
|--
  “ (((Znth ((i - 1 ) - 0 ) (fibfib_prefix_z (i)) 0) + (Znth ((i - 2 ) - 0 ) (fibfib_prefix_z (i)) 0) ) <= INT_MAX) ”
.

Definition fibfib_entail_wit_6_split_goal_3 := 
forall (n0: Z) (ff: Z) (i: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 38)) (PreH3 : (problem_63_pre_z n0 )) (PreH4 : (fibfib_safe_z n0 )) (PreH5 : (ff <> 0)) (PreH6 : (3 <= i)) (PreH7 : (i <= n0)) (PreH8 : ((fibfib_fill_len_z (n0) (i)) = i)) ,
  TT && emp 
|--
  “ (0 <= ((Znth ((i - 1 ) - 0 ) (fibfib_prefix_z (i)) 0) + (Znth ((i - 2 ) - 0 ) (fibfib_prefix_z (i)) 0) )) ”
.

Definition fibfib_entail_wit_6_split_goal_4 := 
forall (n0: Z) (ff: Z) (i: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 38)) (PreH3 : (problem_63_pre_z n0 )) (PreH4 : (fibfib_safe_z n0 )) (PreH5 : (ff <> 0)) (PreH6 : (3 <= i)) (PreH7 : (i <= n0)) (PreH8 : ((fibfib_fill_len_z (n0) (i)) = i)) ,
  TT && emp 
|--
  “ ((Znth ((i - 3 ) - 0 ) (fibfib_prefix_z (i)) 0) = (fibfib_z ((i - 3 )))) ”
.

Definition fibfib_entail_wit_6_split_goal_5 := 
forall (n0: Z) (ff: Z) (i: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 38)) (PreH3 : (problem_63_pre_z n0 )) (PreH4 : (fibfib_safe_z n0 )) (PreH5 : (ff <> 0)) (PreH6 : (3 <= i)) (PreH7 : (i <= n0)) (PreH8 : ((fibfib_fill_len_z (n0) (i)) = i)) ,
  TT && emp 
|--
  “ ((Znth ((i - 2 ) - 0 ) (fibfib_prefix_z (i)) 0) = (fibfib_z ((i - 2 )))) ”
.

Definition fibfib_entail_wit_6_split_goal_6 := 
forall (n0: Z) (ff: Z) (i: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 38)) (PreH3 : (problem_63_pre_z n0 )) (PreH4 : (fibfib_safe_z n0 )) (PreH5 : (ff <> 0)) (PreH6 : (3 <= i)) (PreH7 : (i <= n0)) (PreH8 : ((fibfib_fill_len_z (n0) (i)) = i)) ,
  TT && emp 
|--
  “ ((Znth ((i - 1 ) - 0 ) (fibfib_prefix_z (i)) 0) = (fibfib_z ((i - 1 )))) ”
.

Definition fibfib_entail_wit_6_split_goal_7 := 
forall (n0: Z) (ff: Z) (i: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 38)) (PreH3 : (problem_63_pre_z n0 )) (PreH4 : (fibfib_safe_z n0 )) (PreH5 : (ff <> 0)) (PreH6 : (3 <= i)) (PreH7 : (i <= n0)) (PreH8 : ((fibfib_fill_len_z (n0) (i)) = i)) ,
  TT && emp 
|--
  “ ((app ((fibfib_prefix_z (i))) ((cons ((((Znth ((i - 1 ) - 0 ) (fibfib_prefix_z (i)) 0) + (Znth ((i - 2 ) - 0 ) (fibfib_prefix_z (i)) 0) ) + (Znth ((i - 3 ) - 0 ) (fibfib_prefix_z (i)) 0) )) ((@nil Z))))) = (fibfib_prefix_z ((i + 1 )))) ”
.

Definition fibfib_entail_wit_7 := 
forall (n0: Z) (ff: Z) (i: Z) (a: Z) (b: Z) (c: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 38)) (PreH3 : (problem_63_pre_z n0 )) (PreH4 : (fibfib_safe_z n0 )) (PreH5 : (ff <> 0)) (PreH6 : (3 <= i)) (PreH7 : (i <= n0)) (PreH8 : (a = (fibfib_z ((i - 1 ))))) (PreH9 : (b = (fibfib_z ((i - 2 ))))) (PreH10 : (c = (fibfib_z ((i - 3 ))))) (PreH11 : (0 <= (a + b ))) (PreH12 : ((a + b ) <= INT_MAX)) (PreH13 : ((fibfib_z (i)) = ((a + b ) + c ))) ,
  (IntArray.seg ff 0 (i + 1 ) (fibfib_prefix_z ((i + 1 ))) )
  **  (IntArray.undef_seg ff (i + 1 ) 100 )
|--
  (“ (0 <= n0) ” 
  &&  “ (n0 <= 38) ” 
  &&  “ (problem_63_pre_z n0 ) ” 
  &&  “ (fibfib_safe_z n0 ) ” 
  &&  “ (ff <> 0) ” 
  &&  “ (3 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= 39) ” 
  &&  “ (n0 < 3) ” 
  &&  “ ((i + 1 ) = 3) ”
  &&  (IntArray.seg ff 0 (fibfib_fill_len_z (n0) ((i + 1 ))) (fibfib_prefix_z ((fibfib_fill_len_z (n0) ((i + 1 ))))) )
  **  (IntArray.undef_seg ff (fibfib_fill_len_z (n0) ((i + 1 ))) 100 ))
  ||
  (“ (0 <= n0) ” 
  &&  “ (n0 <= 38) ” 
  &&  “ (problem_63_pre_z n0 ) ” 
  &&  “ (fibfib_safe_z n0 ) ” 
  &&  “ (ff <> 0) ” 
  &&  “ (3 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= 39) ” 
  &&  “ (3 <= n0) ” 
  &&  “ ((i + 1 ) <= (n0 + 1 )) ”
  &&  (IntArray.seg ff 0 (fibfib_fill_len_z (n0) ((i + 1 ))) (fibfib_prefix_z ((fibfib_fill_len_z (n0) ((i + 1 ))))) )
  **  (IntArray.undef_seg ff (fibfib_fill_len_z (n0) ((i + 1 ))) 100 ))
.

Definition fibfib_entail_wit_8_1 := 
(
forall (n0: Z) (i: Z) (ff: Z) (PreH1 : (i > n0)) (PreH2 : (0 <= n0)) (PreH3 : (n0 <= 38)) (PreH4 : (problem_63_pre_z n0 )) (PreH5 : (fibfib_safe_z n0 )) (PreH6 : (ff <> 0)) (PreH7 : (3 <= i)) (PreH8 : (i <= 39)) (PreH9 : (3 <= n0)) (PreH10 : (i <= (n0 + 1 ))) ,
  (IntArray.seg ff 0 (fibfib_fill_len_z (n0) (i)) (fibfib_prefix_z ((fibfib_fill_len_z (n0) (i)))) )
  **  (IntArray.undef_seg ff (fibfib_fill_len_z (n0) (i)) 100 )
|--
  “ (0 <= n0) ” 
  &&  “ (n0 <= 38) ” 
  &&  “ (problem_63_pre_z n0 ) ” 
  &&  “ (fibfib_safe_z n0 ) ” 
  &&  “ (ff <> 0) ”
  &&  (IntArray.seg ff 0 (fibfib_fill_len_z (n0) ((n0 + 1 ))) (fibfib_prefix_z ((fibfib_fill_len_z (n0) ((n0 + 1 ))))) )
  **  (IntArray.undef_seg ff (fibfib_fill_len_z (n0) ((n0 + 1 ))) 100 )
) \/
(
forall (n0: Z) (i: Z) (ff: Z) (PreH1 : (i > n0)) (PreH2 : (0 <= n0)) (PreH3 : (n0 <= 38)) (PreH4 : (problem_63_pre_z n0 )) (PreH5 : (fibfib_safe_z n0 )) (PreH6 : (ff <> 0)) (PreH7 : (3 <= i)) (PreH8 : (i <= 39)) (PreH9 : (3 <= n0)) (PreH10 : (i <= (n0 + 1 ))) ,
  (IntArray.seg ff 0 (fibfib_fill_len_z (n0) (i)) (fibfib_prefix_z ((fibfib_fill_len_z (n0) (i)))) )
  **  (IntArray.undef_seg ff (fibfib_fill_len_z (n0) (i)) 100 )
|--
  (IntArray.seg ff 0 (fibfib_fill_len_z (n0) ((n0 + 1 ))) (fibfib_prefix_z ((fibfib_fill_len_z (n0) ((n0 + 1 ))))) )
  **  (IntArray.undef_seg ff (fibfib_fill_len_z (n0) ((n0 + 1 ))) 100 )
).

Definition fibfib_entail_wit_8_1_split_goal_spatial := 
forall (n0: Z) (i: Z) (ff: Z) (PreH1 : (i > n0)) (PreH2 : (0 <= n0)) (PreH3 : (n0 <= 38)) (PreH4 : (problem_63_pre_z n0 )) (PreH5 : (fibfib_safe_z n0 )) (PreH6 : (ff <> 0)) (PreH7 : (3 <= i)) (PreH8 : (i <= 39)) (PreH9 : (3 <= n0)) (PreH10 : (i <= (n0 + 1 ))) ,
  (IntArray.seg ff 0 (fibfib_fill_len_z (n0) (i)) (fibfib_prefix_z ((fibfib_fill_len_z (n0) (i)))) )
  **  (IntArray.undef_seg ff (fibfib_fill_len_z (n0) (i)) 100 )
|--
  (IntArray.seg ff 0 (fibfib_fill_len_z (n0) ((n0 + 1 ))) (fibfib_prefix_z ((fibfib_fill_len_z (n0) ((n0 + 1 ))))) )
  **  (IntArray.undef_seg ff (fibfib_fill_len_z (n0) ((n0 + 1 ))) 100 )
.

Definition fibfib_entail_wit_8_2 := 
(
forall (n0: Z) (i: Z) (ff: Z) (PreH1 : (i > n0)) (PreH2 : (0 <= n0)) (PreH3 : (n0 <= 38)) (PreH4 : (problem_63_pre_z n0 )) (PreH5 : (fibfib_safe_z n0 )) (PreH6 : (ff <> 0)) (PreH7 : (3 <= i)) (PreH8 : (i <= 39)) (PreH9 : (n0 < 3)) (PreH10 : (i = 3)) ,
  (IntArray.seg ff 0 (fibfib_fill_len_z (n0) (i)) (fibfib_prefix_z ((fibfib_fill_len_z (n0) (i)))) )
  **  (IntArray.undef_seg ff (fibfib_fill_len_z (n0) (i)) 100 )
|--
  “ (0 <= n0) ” 
  &&  “ (n0 <= 38) ” 
  &&  “ (problem_63_pre_z n0 ) ” 
  &&  “ (fibfib_safe_z n0 ) ” 
  &&  “ (ff <> 0) ”
  &&  (IntArray.seg ff 0 (fibfib_fill_len_z (n0) ((n0 + 1 ))) (fibfib_prefix_z ((fibfib_fill_len_z (n0) ((n0 + 1 ))))) )
  **  (IntArray.undef_seg ff (fibfib_fill_len_z (n0) ((n0 + 1 ))) 100 )
) \/
(
forall (n0: Z) (i: Z) (ff: Z) (PreH1 : (i > n0)) (PreH2 : (0 <= n0)) (PreH3 : (n0 <= 38)) (PreH4 : (problem_63_pre_z n0 )) (PreH5 : (fibfib_safe_z n0 )) (PreH6 : (ff <> 0)) (PreH7 : (3 <= i)) (PreH8 : (i <= 39)) (PreH9 : (n0 < 3)) (PreH10 : (i = 3)) ,
  (IntArray.seg ff 0 (fibfib_fill_len_z (n0) (i)) (fibfib_prefix_z ((fibfib_fill_len_z (n0) (i)))) )
  **  (IntArray.undef_seg ff (fibfib_fill_len_z (n0) (i)) 100 )
|--
  (IntArray.seg ff 0 (fibfib_fill_len_z (n0) ((n0 + 1 ))) (fibfib_prefix_z ((fibfib_fill_len_z (n0) ((n0 + 1 ))))) )
  **  (IntArray.undef_seg ff (fibfib_fill_len_z (n0) ((n0 + 1 ))) 100 )
).

Definition fibfib_entail_wit_8_2_split_goal_spatial := 
forall (n0: Z) (i: Z) (ff: Z) (PreH1 : (i > n0)) (PreH2 : (0 <= n0)) (PreH3 : (n0 <= 38)) (PreH4 : (problem_63_pre_z n0 )) (PreH5 : (fibfib_safe_z n0 )) (PreH6 : (ff <> 0)) (PreH7 : (3 <= i)) (PreH8 : (i <= 39)) (PreH9 : (n0 < 3)) (PreH10 : (i = 3)) ,
  (IntArray.seg ff 0 (fibfib_fill_len_z (n0) (i)) (fibfib_prefix_z ((fibfib_fill_len_z (n0) (i)))) )
  **  (IntArray.undef_seg ff (fibfib_fill_len_z (n0) (i)) 100 )
|--
  (IntArray.seg ff 0 (fibfib_fill_len_z (n0) ((n0 + 1 ))) (fibfib_prefix_z ((fibfib_fill_len_z (n0) ((n0 + 1 ))))) )
  **  (IntArray.undef_seg ff (fibfib_fill_len_z (n0) ((n0 + 1 ))) 100 )
.

Definition fibfib_entail_wit_9_1 := 
(
forall (n0: Z) (ff: Z) (PreH1 : (n0 >= 3)) (PreH2 : (0 <= n0)) (PreH3 : (n0 <= 38)) (PreH4 : (problem_63_pre_z n0 )) (PreH5 : (fibfib_safe_z n0 )) (PreH6 : (ff <> 0)) ,
  (IntArray.seg ff 0 (fibfib_fill_len_z (n0) ((n0 + 1 ))) (fibfib_prefix_z ((fibfib_fill_len_z (n0) ((n0 + 1 ))))) )
  **  (IntArray.undef_seg ff (fibfib_fill_len_z (n0) ((n0 + 1 ))) 100 )
|--
  “ ((n0 + 1 ) = (fibfib_fill_len_z (n0) ((n0 + 1 )))) ” 
  &&  “ (n0 < (n0 + 1 )) ” 
  &&  “ (0 <= n0) ” 
  &&  “ (n0 <= 38) ” 
  &&  “ (problem_63_pre_z n0 ) ” 
  &&  “ (fibfib_safe_z n0 ) ” 
  &&  “ (ff <> 0) ” 
  &&  “ ((n0 + 1 ) <= 100) ”
  &&  (IntArray.seg ff 0 (n0 + 1 ) (fibfib_prefix_z ((n0 + 1 ))) )
  **  (IntArray.undef_seg ff (n0 + 1 ) 100 )
) \/
(
forall (n0: Z) (ff: Z) (PreH1 : (n0 >= 3)) (PreH2 : (0 <= n0)) (PreH3 : (n0 <= 38)) (PreH4 : (problem_63_pre_z n0 )) (PreH5 : (fibfib_safe_z n0 )) (PreH6 : (ff <> 0)) ,
  (IntArray.seg ff 0 (fibfib_fill_len_z (n0) ((n0 + 1 ))) (fibfib_prefix_z ((fibfib_fill_len_z (n0) ((n0 + 1 ))))) )
  **  (IntArray.undef_seg ff (fibfib_fill_len_z (n0) ((n0 + 1 ))) 100 )
|--
  “ ((n0 + 1 ) = (fibfib_fill_len_z (n0) ((n0 + 1 )))) ”
  &&  (IntArray.seg ff 0 (n0 + 1 ) (fibfib_prefix_z ((n0 + 1 ))) )
  **  (IntArray.undef_seg ff (n0 + 1 ) 100 )
).

Definition fibfib_entail_wit_9_1_split_goal_1 := 
forall (n0: Z) (ff: Z) (PreH1 : (n0 >= 3)) (PreH2 : (0 <= n0)) (PreH3 : (n0 <= 38)) (PreH4 : (problem_63_pre_z n0 )) (PreH5 : (fibfib_safe_z n0 )) (PreH6 : (ff <> 0)) ,
  (IntArray.seg ff 0 (fibfib_fill_len_z (n0) ((n0 + 1 ))) (fibfib_prefix_z ((fibfib_fill_len_z (n0) ((n0 + 1 ))))) )
  **  (IntArray.undef_seg ff (fibfib_fill_len_z (n0) ((n0 + 1 ))) 100 )
|--
  “ ((n0 + 1 ) = (fibfib_fill_len_z (n0) ((n0 + 1 )))) ”
.

Definition fibfib_entail_wit_9_1_split_goal_spatial := 
forall (n0: Z) (ff: Z) (PreH1 : (n0 >= 3)) (PreH2 : (0 <= n0)) (PreH3 : (n0 <= 38)) (PreH4 : (problem_63_pre_z n0 )) (PreH5 : (fibfib_safe_z n0 )) (PreH6 : (ff <> 0)) ,
  (IntArray.seg ff 0 (fibfib_fill_len_z (n0) ((n0 + 1 ))) (fibfib_prefix_z ((fibfib_fill_len_z (n0) ((n0 + 1 ))))) )
  **  (IntArray.undef_seg ff (fibfib_fill_len_z (n0) ((n0 + 1 ))) 100 )
|--
  (IntArray.seg ff 0 (n0 + 1 ) (fibfib_prefix_z ((n0 + 1 ))) )
  **  (IntArray.undef_seg ff (n0 + 1 ) 100 )
.

Definition fibfib_entail_wit_9_2 := 
(
forall (n0: Z) (ff: Z) (PreH1 : (n0 < 3)) (PreH2 : (0 <= n0)) (PreH3 : (n0 <= 38)) (PreH4 : (problem_63_pre_z n0 )) (PreH5 : (fibfib_safe_z n0 )) (PreH6 : (ff <> 0)) ,
  (IntArray.seg ff 0 (fibfib_fill_len_z (n0) ((n0 + 1 ))) (fibfib_prefix_z ((fibfib_fill_len_z (n0) ((n0 + 1 ))))) )
  **  (IntArray.undef_seg ff (fibfib_fill_len_z (n0) ((n0 + 1 ))) 100 )
|--
  “ (3 = (fibfib_fill_len_z (n0) ((n0 + 1 )))) ” 
  &&  “ (n0 < 3) ” 
  &&  “ (0 <= n0) ” 
  &&  “ (n0 <= 38) ” 
  &&  “ (problem_63_pre_z n0 ) ” 
  &&  “ (fibfib_safe_z n0 ) ” 
  &&  “ (ff <> 0) ” 
  &&  “ (3 <= 100) ”
  &&  (IntArray.seg ff 0 3 (fibfib_prefix_z (3)) )
  **  (IntArray.undef_seg ff 3 100 )
) \/
(
forall (n0: Z) (ff: Z) (PreH1 : (n0 < 3)) (PreH2 : (0 <= n0)) (PreH3 : (n0 <= 38)) (PreH4 : (problem_63_pre_z n0 )) (PreH5 : (fibfib_safe_z n0 )) (PreH6 : (ff <> 0)) ,
  (IntArray.seg ff 0 (fibfib_fill_len_z (n0) ((n0 + 1 ))) (fibfib_prefix_z ((fibfib_fill_len_z (n0) ((n0 + 1 ))))) )
  **  (IntArray.undef_seg ff (fibfib_fill_len_z (n0) ((n0 + 1 ))) 100 )
|--
  “ (3 = (fibfib_fill_len_z (n0) ((n0 + 1 )))) ”
  &&  (IntArray.seg ff 0 3 (fibfib_prefix_z (3)) )
  **  (IntArray.undef_seg ff 3 100 )
).

Definition fibfib_entail_wit_9_2_split_goal_1 := 
forall (n0: Z) (ff: Z) (PreH1 : (n0 < 3)) (PreH2 : (0 <= n0)) (PreH3 : (n0 <= 38)) (PreH4 : (problem_63_pre_z n0 )) (PreH5 : (fibfib_safe_z n0 )) (PreH6 : (ff <> 0)) ,
  (IntArray.seg ff 0 (fibfib_fill_len_z (n0) ((n0 + 1 ))) (fibfib_prefix_z ((fibfib_fill_len_z (n0) ((n0 + 1 ))))) )
  **  (IntArray.undef_seg ff (fibfib_fill_len_z (n0) ((n0 + 1 ))) 100 )
|--
  “ (3 = (fibfib_fill_len_z (n0) ((n0 + 1 )))) ”
.

Definition fibfib_entail_wit_9_2_split_goal_spatial := 
forall (n0: Z) (ff: Z) (PreH1 : (n0 < 3)) (PreH2 : (0 <= n0)) (PreH3 : (n0 <= 38)) (PreH4 : (problem_63_pre_z n0 )) (PreH5 : (fibfib_safe_z n0 )) (PreH6 : (ff <> 0)) ,
  (IntArray.seg ff 0 (fibfib_fill_len_z (n0) ((n0 + 1 ))) (fibfib_prefix_z ((fibfib_fill_len_z (n0) ((n0 + 1 ))))) )
  **  (IntArray.undef_seg ff (fibfib_fill_len_z (n0) ((n0 + 1 ))) 100 )
|--
  (IntArray.seg ff 0 3 (fibfib_prefix_z (3)) )
  **  (IntArray.undef_seg ff 3 100 )
.

Definition fibfib_entail_wit_10 := 
(
forall (n0: Z) (filled: Z) (ff: Z) (PreH1 : (filled = (fibfib_fill_len_z (n0) ((n0 + 1 ))))) (PreH2 : (n0 < filled)) (PreH3 : (0 <= n0)) (PreH4 : (n0 <= 38)) (PreH5 : (problem_63_pre_z n0 )) (PreH6 : (fibfib_safe_z n0 )) (PreH7 : (ff <> 0)) (PreH8 : (filled <= 100)) ,
  (IntArray.seg ff 0 filled (fibfib_prefix_z (filled)) )
  **  (IntArray.undef_seg ff filled 100 )
|--
  “ ((Znth (n0 - 0 ) (fibfib_prefix_z (filled)) 0) = (fibfib_z (n0))) ” 
  &&  “ (filled = (fibfib_fill_len_z (n0) ((n0 + 1 )))) ” 
  &&  “ (n0 < filled) ” 
  &&  “ (0 <= n0) ” 
  &&  “ (n0 <= 38) ” 
  &&  “ (problem_63_pre_z n0 ) ” 
  &&  “ (fibfib_safe_z n0 ) ” 
  &&  “ (ff <> 0) ” 
  &&  “ (filled <= 100) ”
  &&  (IntArray.seg ff 0 filled (fibfib_prefix_z (filled)) )
  **  (IntArray.undef_seg ff filled 100 )
) \/
(
forall (n0: Z) (filled: Z) (ff: Z) (PreH1 : (filled = (fibfib_fill_len_z (n0) ((n0 + 1 ))))) (PreH2 : (n0 < filled)) (PreH3 : (0 <= n0)) (PreH4 : (n0 <= 38)) (PreH5 : (problem_63_pre_z n0 )) (PreH6 : (fibfib_safe_z n0 )) (PreH7 : (ff <> 0)) (PreH8 : (filled <= 100)) ,
  TT && emp 
|--
  “ ((Znth (n0 - 0 ) (fibfib_prefix_z (filled)) 0) = (fibfib_z (n0))) ”
  &&  emp
).

Definition fibfib_entail_wit_10_split_goal_1 := 
forall (n0: Z) (filled: Z) (ff: Z) (PreH1 : (filled = (fibfib_fill_len_z (n0) ((n0 + 1 ))))) (PreH2 : (n0 < filled)) (PreH3 : (0 <= n0)) (PreH4 : (n0 <= 38)) (PreH5 : (problem_63_pre_z n0 )) (PreH6 : (fibfib_safe_z n0 )) (PreH7 : (ff <> 0)) (PreH8 : (filled <= 100)) ,
  TT && emp 
|--
  “ ((Znth (n0 - 0 ) (fibfib_prefix_z (filled)) 0) = (fibfib_z (n0))) ”
.

Definition fibfib_return_wit_1 := 
(
forall (n0: Z) (result: Z) (filled: Z) (ff: Z) (PreH1 : (result = (fibfib_z (n0)))) (PreH2 : (filled = (fibfib_fill_len_z (n0) ((n0 + 1 ))))) (PreH3 : (n0 < filled)) (PreH4 : (0 <= n0)) (PreH5 : (n0 <= 38)) (PreH6 : (problem_63_pre_z n0 )) (PreH7 : (fibfib_safe_z n0 )) (PreH8 : (ff <> 0)) (PreH9 : (filled <= 100)) ,
  TT && emp 
|--
  “ (problem_63_spec_z n0 result ) ”
  &&  emp
) \/
(
forall (n0: Z) (result: Z) (filled: Z) (ff: Z) (PreH1 : (result = (fibfib_z (n0)))) (PreH2 : (filled = (fibfib_fill_len_z (n0) ((n0 + 1 ))))) (PreH3 : (n0 < filled)) (PreH4 : (0 <= n0)) (PreH5 : (n0 <= 38)) (PreH6 : (problem_63_pre_z n0 )) (PreH7 : (fibfib_safe_z n0 )) (PreH8 : (ff <> 0)) (PreH9 : (filled <= 100)) ,
  TT && emp 
|--
  “ (problem_63_spec_z n0 result ) ”
  &&  emp
).

Definition fibfib_return_wit_1_split_goal_1 := 
forall (n0: Z) (result: Z) (filled: Z) (ff: Z) (PreH1 : (result = (fibfib_z (n0)))) (PreH2 : (filled = (fibfib_fill_len_z (n0) ((n0 + 1 ))))) (PreH3 : (n0 < filled)) (PreH4 : (0 <= n0)) (PreH5 : (n0 <= 38)) (PreH6 : (problem_63_pre_z n0 )) (PreH7 : (fibfib_safe_z n0 )) (PreH8 : (ff <> 0)) (PreH9 : (filled <= 100)) ,
  TT && emp 
|--
  “ (problem_63_spec_z n0 result ) ”
.

Definition fibfib_partial_solve_wit_1_pure := 
forall (n_pre: Z) (n0: Z) (PreH1 : (n_pre = n0)) (PreH2 : (0 <= n0)) (PreH3 : (n0 <= 38)) (PreH4 : (problem_63_pre_z n0 )) (PreH5 : (fibfib_safe_z n0 )) ,
  ((( &( "ff" ) )) # Ptr  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (100 = 100) ”
.

Definition fibfib_partial_solve_wit_1_aux := 
forall (n_pre: Z) (n0: Z) (PreH1 : (n_pre = n0)) (PreH2 : (0 <= n0)) (PreH3 : (n0 <= 38)) (PreH4 : (problem_63_pre_z n0 )) (PreH5 : (fibfib_safe_z n0 )) ,
  TT && emp 
|--
  “ (100 = 100) ” 
  &&  “ (n_pre = n0) ” 
  &&  “ (0 <= n0) ” 
  &&  “ (n0 <= 38) ” 
  &&  “ (problem_63_pre_z n0 ) ” 
  &&  “ (fibfib_safe_z n0 ) ”
  &&  emp
.

Definition fibfib_partial_solve_wit_1 := fibfib_partial_solve_wit_1_pure -> fibfib_partial_solve_wit_1_aux.

Definition fibfib_partial_solve_wit_2 := 
forall (n_pre: Z) (n0: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (n_pre = n0)) (PreH3 : (0 <= n0)) (PreH4 : (n0 <= 38)) (PreH5 : (problem_63_pre_z n0 )) (PreH6 : (fibfib_safe_z n0 )) ,
  (IntArray.undef_full retval 100 )
|--
  “ (retval <> 0) ” 
  &&  “ (n_pre = n0) ” 
  &&  “ (0 <= n0) ” 
  &&  “ (n0 <= 38) ” 
  &&  “ (problem_63_pre_z n0 ) ” 
  &&  “ (fibfib_safe_z n0 ) ”
  &&  (((retval + (0 * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg retval 1 100 )
.

Definition fibfib_partial_solve_wit_3 := 
forall (n0: Z) (ff: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 38)) (PreH3 : (problem_63_pre_z n0 )) (PreH4 : (fibfib_safe_z n0 )) (PreH5 : (ff <> 0)) ,
  (IntArray.seg ff 0 1 (cons (0) ((@nil Z))) )
  **  (IntArray.undef_seg ff 1 100 )
|--
  “ (0 <= n0) ” 
  &&  “ (n0 <= 38) ” 
  &&  “ (problem_63_pre_z n0 ) ” 
  &&  “ (fibfib_safe_z n0 ) ” 
  &&  “ (ff <> 0) ”
  &&  (((ff + (1 * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg ff (1 + 1 ) 100 )
  **  (IntArray.seg ff 0 1 (cons (0) ((@nil Z))) )
.

Definition fibfib_partial_solve_wit_4 := 
forall (n0: Z) (ff: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 38)) (PreH3 : (problem_63_pre_z n0 )) (PreH4 : (fibfib_safe_z n0 )) (PreH5 : (ff <> 0)) ,
  (IntArray.seg ff 0 2 (cons (0) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg ff 2 100 )
|--
  “ (0 <= n0) ” 
  &&  “ (n0 <= 38) ” 
  &&  “ (problem_63_pre_z n0 ) ” 
  &&  “ (fibfib_safe_z n0 ) ” 
  &&  “ (ff <> 0) ”
  &&  (((ff + (2 * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg ff (2 + 1 ) 100 )
  **  (IntArray.seg ff 0 2 (cons (0) ((cons (0) ((@nil Z))))) )
.

Definition fibfib_partial_solve_wit_5 := 
forall (n0: Z) (ff: Z) (i: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 38)) (PreH3 : (problem_63_pre_z n0 )) (PreH4 : (fibfib_safe_z n0 )) (PreH5 : (ff <> 0)) (PreH6 : (3 <= i)) (PreH7 : (i <= n0)) (PreH8 : ((fibfib_fill_len_z (n0) (i)) = i)) ,
  (IntArray.seg ff 0 i (fibfib_prefix_z (i)) )
  **  (IntArray.undef_seg ff i 100 )
|--
  “ (0 <= n0) ” 
  &&  “ (n0 <= 38) ” 
  &&  “ (problem_63_pre_z n0 ) ” 
  &&  “ (fibfib_safe_z n0 ) ” 
  &&  “ (ff <> 0) ” 
  &&  “ (3 <= i) ” 
  &&  “ (i <= n0) ” 
  &&  “ ((fibfib_fill_len_z (n0) (i)) = i) ”
  &&  (((ff + ((i - 1 ) * sizeof(INT) ) )) # Int  |-> (Znth ((i - 1 ) - 0 ) (fibfib_prefix_z (i)) 0))
  **  (IntArray.missing_i ff (i - 1 ) 0 i (fibfib_prefix_z (i)) )
  **  (IntArray.undef_seg ff i 100 )
.

Definition fibfib_partial_solve_wit_6 := 
forall (n0: Z) (ff: Z) (i: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 38)) (PreH3 : (problem_63_pre_z n0 )) (PreH4 : (fibfib_safe_z n0 )) (PreH5 : (ff <> 0)) (PreH6 : (3 <= i)) (PreH7 : (i <= n0)) (PreH8 : ((fibfib_fill_len_z (n0) (i)) = i)) ,
  (IntArray.seg ff 0 i (fibfib_prefix_z (i)) )
  **  (IntArray.undef_seg ff i 100 )
|--
  “ (0 <= n0) ” 
  &&  “ (n0 <= 38) ” 
  &&  “ (problem_63_pre_z n0 ) ” 
  &&  “ (fibfib_safe_z n0 ) ” 
  &&  “ (ff <> 0) ” 
  &&  “ (3 <= i) ” 
  &&  “ (i <= n0) ” 
  &&  “ ((fibfib_fill_len_z (n0) (i)) = i) ”
  &&  (((ff + ((i - 2 ) * sizeof(INT) ) )) # Int  |-> (Znth ((i - 2 ) - 0 ) (fibfib_prefix_z (i)) 0))
  **  (IntArray.missing_i ff (i - 2 ) 0 i (fibfib_prefix_z (i)) )
  **  (IntArray.undef_seg ff i 100 )
.

Definition fibfib_partial_solve_wit_7 := 
forall (n0: Z) (ff: Z) (i: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 38)) (PreH3 : (problem_63_pre_z n0 )) (PreH4 : (fibfib_safe_z n0 )) (PreH5 : (ff <> 0)) (PreH6 : (3 <= i)) (PreH7 : (i <= n0)) (PreH8 : ((fibfib_fill_len_z (n0) (i)) = i)) ,
  (IntArray.seg ff 0 i (fibfib_prefix_z (i)) )
  **  (IntArray.undef_seg ff i 100 )
|--
  “ (0 <= n0) ” 
  &&  “ (n0 <= 38) ” 
  &&  “ (problem_63_pre_z n0 ) ” 
  &&  “ (fibfib_safe_z n0 ) ” 
  &&  “ (ff <> 0) ” 
  &&  “ (3 <= i) ” 
  &&  “ (i <= n0) ” 
  &&  “ ((fibfib_fill_len_z (n0) (i)) = i) ”
  &&  (((ff + ((i - 3 ) * sizeof(INT) ) )) # Int  |-> (Znth ((i - 3 ) - 0 ) (fibfib_prefix_z (i)) 0))
  **  (IntArray.missing_i ff (i - 3 ) 0 i (fibfib_prefix_z (i)) )
  **  (IntArray.undef_seg ff i 100 )
.

Definition fibfib_partial_solve_wit_8 := 
forall (n0: Z) (ff: Z) (i: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 38)) (PreH3 : (problem_63_pre_z n0 )) (PreH4 : (fibfib_safe_z n0 )) (PreH5 : (ff <> 0)) (PreH6 : (3 <= i)) (PreH7 : (i <= n0)) (PreH8 : ((fibfib_fill_len_z (n0) (i)) = i)) ,
  (IntArray.seg ff 0 i (fibfib_prefix_z (i)) )
  **  (IntArray.undef_seg ff i 100 )
|--
  “ (0 <= n0) ” 
  &&  “ (n0 <= 38) ” 
  &&  “ (problem_63_pre_z n0 ) ” 
  &&  “ (fibfib_safe_z n0 ) ” 
  &&  “ (ff <> 0) ” 
  &&  “ (3 <= i) ” 
  &&  “ (i <= n0) ” 
  &&  “ ((fibfib_fill_len_z (n0) (i)) = i) ”
  &&  (((ff + (i * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg ff (i + 1 ) 100 )
  **  (IntArray.seg ff 0 i (fibfib_prefix_z (i)) )
.

Definition fibfib_partial_solve_wit_9 := 
forall (n0: Z) (filled: Z) (ff: Z) (PreH1 : (filled = (fibfib_fill_len_z (n0) ((n0 + 1 ))))) (PreH2 : (n0 < filled)) (PreH3 : (0 <= n0)) (PreH4 : (n0 <= 38)) (PreH5 : (problem_63_pre_z n0 )) (PreH6 : (fibfib_safe_z n0 )) (PreH7 : (ff <> 0)) (PreH8 : (filled <= 100)) ,
  (IntArray.seg ff 0 filled (fibfib_prefix_z (filled)) )
  **  (IntArray.undef_seg ff filled 100 )
|--
  “ (filled = (fibfib_fill_len_z (n0) ((n0 + 1 )))) ” 
  &&  “ (n0 < filled) ” 
  &&  “ (0 <= n0) ” 
  &&  “ (n0 <= 38) ” 
  &&  “ (problem_63_pre_z n0 ) ” 
  &&  “ (fibfib_safe_z n0 ) ” 
  &&  “ (ff <> 0) ” 
  &&  “ (filled <= 100) ”
  &&  (((ff + (n0 * sizeof(INT) ) )) # Int  |-> (Znth (n0 - 0 ) (fibfib_prefix_z (filled)) 0))
  **  (IntArray.missing_i ff n0 0 filled (fibfib_prefix_z (filled)) )
  **  (IntArray.undef_seg ff filled 100 )
.

Definition fibfib_partial_solve_wit_10_pure := 
forall (n0: Z) (result: Z) (filled: Z) (ff: Z) (PreH1 : (result = (fibfib_z (n0)))) (PreH2 : (filled = (fibfib_fill_len_z (n0) ((n0 + 1 ))))) (PreH3 : (n0 < filled)) (PreH4 : (0 <= n0)) (PreH5 : (n0 <= 38)) (PreH6 : (problem_63_pre_z n0 )) (PreH7 : (fibfib_safe_z n0 )) (PreH8 : (ff <> 0)) (PreH9 : (filled <= 100)) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "result" ) )) # Int  |-> result)
  **  ((( &( "filled" ) )) # Int  |-> filled)
  **  ((( &( "ff" ) )) # Ptr  |-> ff)
  **  (IntArray.seg ff 0 filled (fibfib_prefix_z (filled)) )
  **  (IntArray.undef_seg ff filled 100 )
|--
  “ (ff <> 0) ” 
  &&  “ (0 <= filled) ” 
  &&  “ (filled <= 100) ” 
  &&  “ (100 = 100) ”
.

Definition fibfib_partial_solve_wit_10_aux := 
forall (n0: Z) (result: Z) (filled: Z) (ff: Z) (PreH1 : (result = (fibfib_z (n0)))) (PreH2 : (filled = (fibfib_fill_len_z (n0) ((n0 + 1 ))))) (PreH3 : (n0 < filled)) (PreH4 : (0 <= n0)) (PreH5 : (n0 <= 38)) (PreH6 : (problem_63_pre_z n0 )) (PreH7 : (fibfib_safe_z n0 )) (PreH8 : (ff <> 0)) (PreH9 : (filled <= 100)) ,
  (IntArray.seg ff 0 filled (fibfib_prefix_z (filled)) )
  **  (IntArray.undef_seg ff filled 100 )
|--
  “ (ff <> 0) ” 
  &&  “ (0 <= filled) ” 
  &&  “ (filled <= 100) ” 
  &&  “ (100 = 100) ” 
  &&  “ (result = (fibfib_z (n0))) ” 
  &&  “ (filled = (fibfib_fill_len_z (n0) ((n0 + 1 )))) ” 
  &&  “ (n0 < filled) ” 
  &&  “ (0 <= n0) ” 
  &&  “ (n0 <= 38) ” 
  &&  “ (problem_63_pre_z n0 ) ” 
  &&  “ (fibfib_safe_z n0 ) ” 
  &&  “ (ff <> 0) ” 
  &&  “ (filled <= 100) ”
  &&  (IntArray.seg ff 0 filled (fibfib_prefix_z (filled)) )
  **  (IntArray.undef_seg ff filled 100 )
.

Definition fibfib_partial_solve_wit_10 := fibfib_partial_solve_wit_10_pure -> fibfib_partial_solve_wit_10_aux.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_fibfib_safety_wit_1 : fibfib_safety_wit_1.
Axiom proof_of_fibfib_safety_wit_2 : fibfib_safety_wit_2.
Axiom proof_of_fibfib_safety_wit_3 : fibfib_safety_wit_3.
Axiom proof_of_fibfib_safety_wit_4 : fibfib_safety_wit_4.
Axiom proof_of_fibfib_safety_wit_5 : fibfib_safety_wit_5.
Axiom proof_of_fibfib_safety_wit_6 : fibfib_safety_wit_6.
Axiom proof_of_fibfib_safety_wit_7 : fibfib_safety_wit_7.
Axiom proof_of_fibfib_safety_wit_8 : fibfib_safety_wit_8.
Axiom proof_of_fibfib_safety_wit_9 : fibfib_safety_wit_9.
Axiom proof_of_fibfib_safety_wit_10 : fibfib_safety_wit_10.
Axiom proof_of_fibfib_safety_wit_11 : fibfib_safety_wit_11.
Axiom proof_of_fibfib_safety_wit_12 : fibfib_safety_wit_12.
Axiom proof_of_fibfib_safety_wit_13 : fibfib_safety_wit_13.
Axiom proof_of_fibfib_safety_wit_14 : fibfib_safety_wit_14.
Axiom proof_of_fibfib_safety_wit_15 : fibfib_safety_wit_15.
Axiom proof_of_fibfib_safety_wit_16 : fibfib_safety_wit_16.
Axiom proof_of_fibfib_safety_wit_17 : fibfib_safety_wit_17.
Axiom proof_of_fibfib_safety_wit_18 : fibfib_safety_wit_18.
Axiom proof_of_fibfib_safety_wit_19 : fibfib_safety_wit_19.
Axiom proof_of_fibfib_safety_wit_20 : fibfib_safety_wit_20.
Axiom proof_of_fibfib_safety_wit_21 : fibfib_safety_wit_21.
Axiom proof_of_fibfib_safety_wit_22 : fibfib_safety_wit_22.
Axiom proof_of_fibfib_safety_wit_23 : fibfib_safety_wit_23.
Axiom proof_of_fibfib_entail_wit_1 : fibfib_entail_wit_1.
Axiom proof_of_fibfib_entail_wit_2 : fibfib_entail_wit_2.
Axiom proof_of_fibfib_entail_wit_3 : fibfib_entail_wit_3.
Axiom proof_of_fibfib_entail_wit_4 : fibfib_entail_wit_4.
Axiom proof_of_fibfib_entail_wit_5 : fibfib_entail_wit_5.
Axiom proof_of_fibfib_entail_wit_6 : fibfib_entail_wit_6.
Axiom proof_of_fibfib_entail_wit_7 : fibfib_entail_wit_7.
Axiom proof_of_fibfib_entail_wit_8_1 : fibfib_entail_wit_8_1.
Axiom proof_of_fibfib_entail_wit_8_2 : fibfib_entail_wit_8_2.
Axiom proof_of_fibfib_entail_wit_9_1 : fibfib_entail_wit_9_1.
Axiom proof_of_fibfib_entail_wit_9_2 : fibfib_entail_wit_9_2.
Axiom proof_of_fibfib_entail_wit_10 : fibfib_entail_wit_10.
Axiom proof_of_fibfib_return_wit_1 : fibfib_return_wit_1.
Axiom proof_of_fibfib_partial_solve_wit_1_pure : fibfib_partial_solve_wit_1_pure.
Axiom proof_of_fibfib_partial_solve_wit_1 : fibfib_partial_solve_wit_1.
Axiom proof_of_fibfib_partial_solve_wit_2 : fibfib_partial_solve_wit_2.
Axiom proof_of_fibfib_partial_solve_wit_3 : fibfib_partial_solve_wit_3.
Axiom proof_of_fibfib_partial_solve_wit_4 : fibfib_partial_solve_wit_4.
Axiom proof_of_fibfib_partial_solve_wit_5 : fibfib_partial_solve_wit_5.
Axiom proof_of_fibfib_partial_solve_wit_6 : fibfib_partial_solve_wit_6.
Axiom proof_of_fibfib_partial_solve_wit_7 : fibfib_partial_solve_wit_7.
Axiom proof_of_fibfib_partial_solve_wit_8 : fibfib_partial_solve_wit_8.
Axiom proof_of_fibfib_partial_solve_wit_9 : fibfib_partial_solve_wit_9.
Axiom proof_of_fibfib_partial_solve_wit_10_pure : fibfib_partial_solve_wit_10_pure.
Axiom proof_of_fibfib_partial_solve_wit_10 : fibfib_partial_solve_wit_10.

End VC_Correct.
