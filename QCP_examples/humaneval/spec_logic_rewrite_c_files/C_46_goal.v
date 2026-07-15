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
Require Import coins_46.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_proof.

(*----- Function fib4 -----*)

Definition fib4_safety_wit_1 := 
forall (n_pre: Z) (n0: Z) (PreH1 : (n_pre = n0)) (PreH2 : (0 <= n0)) (PreH3 : (n0 <= 35)) (PreH4 : (problem_46_pre_z n0 )) (PreH5 : (fib4_safe_z n0 )) ,
  ((( &( "f" ) )) # Ptr  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (100 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 100) ”
.

Definition fib4_safety_wit_2 := 
forall (n_pre: Z) (n0: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (n_pre = n0)) (PreH3 : (0 <= n0)) (PreH4 : (n0 <= 35)) (PreH5 : (problem_46_pre_z n0 )) (PreH6 : (fib4_safe_z n0 )) ,
  (IntArray.undef_full retval 100 )
  **  ((( &( "f" ) )) # Ptr  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition fib4_safety_wit_3 := 
forall (n_pre: Z) (n0: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (n_pre = n0)) (PreH3 : (0 <= n0)) (PreH4 : (n0 <= 35)) (PreH5 : (problem_46_pre_z n0 )) (PreH6 : (fib4_safe_z n0 )) ,
  (IntArray.undef_full retval 100 )
  **  ((( &( "f" ) )) # Ptr  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition fib4_safety_wit_4 := 
forall (n0: Z) (f: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 35)) (PreH3 : (problem_46_pre_z n0 )) (PreH4 : (fib4_safe_z n0 )) (PreH5 : (f <> 0)) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "f" ) )) # Ptr  |-> f)
  **  (IntArray.seg f 0 1 (cons (0) ((@nil Z))) )
  **  (IntArray.undef_seg f 1 100 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition fib4_safety_wit_5 := 
forall (n0: Z) (f: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 35)) (PreH3 : (problem_46_pre_z n0 )) (PreH4 : (fib4_safe_z n0 )) (PreH5 : (f <> 0)) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "f" ) )) # Ptr  |-> f)
  **  (IntArray.seg f 0 1 (cons (0) ((@nil Z))) )
  **  (IntArray.undef_seg f 1 100 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition fib4_safety_wit_6 := 
forall (n0: Z) (f: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 35)) (PreH3 : (problem_46_pre_z n0 )) (PreH4 : (fib4_safe_z n0 )) (PreH5 : (f <> 0)) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "f" ) )) # Ptr  |-> f)
  **  (IntArray.seg f 0 2 (cons (0) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg f 2 100 )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition fib4_safety_wit_7 := 
forall (n0: Z) (f: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 35)) (PreH3 : (problem_46_pre_z n0 )) (PreH4 : (fib4_safe_z n0 )) (PreH5 : (f <> 0)) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "f" ) )) # Ptr  |-> f)
  **  (IntArray.seg f 0 2 (cons (0) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg f 2 100 )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition fib4_safety_wit_8 := 
forall (n0: Z) (f: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 35)) (PreH3 : (problem_46_pre_z n0 )) (PreH4 : (fib4_safe_z n0 )) (PreH5 : (f <> 0)) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "f" ) )) # Ptr  |-> f)
  **  (IntArray.seg f 0 3 (cons (0) ((cons (0) ((cons (2) ((@nil Z))))))) )
  **  (IntArray.undef_seg f 3 100 )
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition fib4_safety_wit_9 := 
forall (n0: Z) (f: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 35)) (PreH3 : (problem_46_pre_z n0 )) (PreH4 : (fib4_safe_z n0 )) (PreH5 : (f <> 0)) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "f" ) )) # Ptr  |-> f)
  **  (IntArray.seg f 0 3 (cons (0) ((cons (0) ((cons (2) ((@nil Z))))))) )
  **  (IntArray.undef_seg f 3 100 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition fib4_safety_wit_10 := 
forall (n0: Z) (f: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 35)) (PreH3 : (problem_46_pre_z n0 )) (PreH4 : (fib4_safe_z n0 )) (PreH5 : (f <> 0)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "f" ) )) # Ptr  |-> f)
  **  (IntArray.seg f 0 4 (fib4_prefix_z (4)) )
  **  (IntArray.undef_seg f 4 100 )
|--
  “ (4 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 4) ”
.

Definition fib4_safety_wit_11 := 
forall (n0: Z) (i: Z) (f: Z) (PreH1 : (i <= n0)) (PreH2 : (0 <= n0)) (PreH3 : (n0 <= 35)) (PreH4 : (problem_46_pre_z n0 )) (PreH5 : (fib4_safe_z n0 )) (PreH6 : (f <> 0)) (PreH7 : (4 <= i)) (PreH8 : (i <= 36)) (PreH9 : (n0 < 4)) (PreH10 : (i = 4)) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "f" ) )) # Ptr  |-> f)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.seg f 0 (fib4_fill_len_z (n0) (i)) (fib4_prefix_z ((fib4_fill_len_z (n0) (i)))) )
  **  (IntArray.undef_seg f (fib4_fill_len_z (n0) (i)) 100 )
|--
  “ False ”
.

Definition fib4_safety_wit_12 := 
forall (n0: Z) (f: Z) (i: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 35)) (PreH3 : (problem_46_pre_z n0 )) (PreH4 : (fib4_safe_z n0 )) (PreH5 : (f <> 0)) (PreH6 : (4 <= i)) (PreH7 : (i <= n0)) (PreH8 : ((fib4_fill_len_z (n0) (i)) = i)) ,
  ((( &( "a" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "f" ) )) # Ptr  |-> f)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.seg f 0 i (fib4_prefix_z (i)) )
  **  (IntArray.undef_seg f i 100 )
|--
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition fib4_safety_wit_13 := 
forall (n0: Z) (f: Z) (i: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 35)) (PreH3 : (problem_46_pre_z n0 )) (PreH4 : (fib4_safe_z n0 )) (PreH5 : (f <> 0)) (PreH6 : (4 <= i)) (PreH7 : (i <= n0)) (PreH8 : ((fib4_fill_len_z (n0) (i)) = i)) ,
  ((( &( "a" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "f" ) )) # Ptr  |-> f)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.seg f 0 i (fib4_prefix_z (i)) )
  **  (IntArray.undef_seg f i 100 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition fib4_safety_wit_14 := 
forall (n0: Z) (f: Z) (i: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 35)) (PreH3 : (problem_46_pre_z n0 )) (PreH4 : (fib4_safe_z n0 )) (PreH5 : (f <> 0)) (PreH6 : (4 <= i)) (PreH7 : (i <= n0)) (PreH8 : ((fib4_fill_len_z (n0) (i)) = i)) ,
  ((( &( "b" ) )) # Int  |->_)
  **  (IntArray.seg f 0 i (fib4_prefix_z (i)) )
  **  ((( &( "a" ) )) # Int  |-> (Znth ((i - 1 ) - 0 ) (fib4_prefix_z (i)) 0))
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "f" ) )) # Ptr  |-> f)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_seg f i 100 )
|--
  “ ((i - 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 2 )) ”
.

Definition fib4_safety_wit_15 := 
forall (n0: Z) (f: Z) (i: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 35)) (PreH3 : (problem_46_pre_z n0 )) (PreH4 : (fib4_safe_z n0 )) (PreH5 : (f <> 0)) (PreH6 : (4 <= i)) (PreH7 : (i <= n0)) (PreH8 : ((fib4_fill_len_z (n0) (i)) = i)) ,
  ((( &( "b" ) )) # Int  |->_)
  **  (IntArray.seg f 0 i (fib4_prefix_z (i)) )
  **  ((( &( "a" ) )) # Int  |-> (Znth ((i - 1 ) - 0 ) (fib4_prefix_z (i)) 0))
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "f" ) )) # Ptr  |-> f)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_seg f i 100 )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition fib4_safety_wit_16 := 
forall (n0: Z) (f: Z) (i: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 35)) (PreH3 : (problem_46_pre_z n0 )) (PreH4 : (fib4_safe_z n0 )) (PreH5 : (f <> 0)) (PreH6 : (4 <= i)) (PreH7 : (i <= n0)) (PreH8 : ((fib4_fill_len_z (n0) (i)) = i)) ,
  ((( &( "c" ) )) # Int  |->_)
  **  (IntArray.seg f 0 i (fib4_prefix_z (i)) )
  **  ((( &( "b" ) )) # Int  |-> (Znth ((i - 2 ) - 0 ) (fib4_prefix_z (i)) 0))
  **  ((( &( "a" ) )) # Int  |-> (Znth ((i - 1 ) - 0 ) (fib4_prefix_z (i)) 0))
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "f" ) )) # Ptr  |-> f)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_seg f i 100 )
|--
  “ ((i - 3 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 3 )) ”
.

Definition fib4_safety_wit_17 := 
forall (n0: Z) (f: Z) (i: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 35)) (PreH3 : (problem_46_pre_z n0 )) (PreH4 : (fib4_safe_z n0 )) (PreH5 : (f <> 0)) (PreH6 : (4 <= i)) (PreH7 : (i <= n0)) (PreH8 : ((fib4_fill_len_z (n0) (i)) = i)) ,
  ((( &( "c" ) )) # Int  |->_)
  **  (IntArray.seg f 0 i (fib4_prefix_z (i)) )
  **  ((( &( "b" ) )) # Int  |-> (Znth ((i - 2 ) - 0 ) (fib4_prefix_z (i)) 0))
  **  ((( &( "a" ) )) # Int  |-> (Znth ((i - 1 ) - 0 ) (fib4_prefix_z (i)) 0))
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "f" ) )) # Ptr  |-> f)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_seg f i 100 )
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition fib4_safety_wit_18 := 
forall (n0: Z) (f: Z) (i: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 35)) (PreH3 : (problem_46_pre_z n0 )) (PreH4 : (fib4_safe_z n0 )) (PreH5 : (f <> 0)) (PreH6 : (4 <= i)) (PreH7 : (i <= n0)) (PreH8 : ((fib4_fill_len_z (n0) (i)) = i)) ,
  ((( &( "d" ) )) # Int  |->_)
  **  (IntArray.seg f 0 i (fib4_prefix_z (i)) )
  **  ((( &( "c" ) )) # Int  |-> (Znth ((i - 3 ) - 0 ) (fib4_prefix_z (i)) 0))
  **  ((( &( "b" ) )) # Int  |-> (Znth ((i - 2 ) - 0 ) (fib4_prefix_z (i)) 0))
  **  ((( &( "a" ) )) # Int  |-> (Znth ((i - 1 ) - 0 ) (fib4_prefix_z (i)) 0))
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "f" ) )) # Ptr  |-> f)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_seg f i 100 )
|--
  “ ((i - 4 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 4 )) ”
.

Definition fib4_safety_wit_19 := 
forall (n0: Z) (f: Z) (i: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 35)) (PreH3 : (problem_46_pre_z n0 )) (PreH4 : (fib4_safe_z n0 )) (PreH5 : (f <> 0)) (PreH6 : (4 <= i)) (PreH7 : (i <= n0)) (PreH8 : ((fib4_fill_len_z (n0) (i)) = i)) ,
  ((( &( "d" ) )) # Int  |->_)
  **  (IntArray.seg f 0 i (fib4_prefix_z (i)) )
  **  ((( &( "c" ) )) # Int  |-> (Znth ((i - 3 ) - 0 ) (fib4_prefix_z (i)) 0))
  **  ((( &( "b" ) )) # Int  |-> (Znth ((i - 2 ) - 0 ) (fib4_prefix_z (i)) 0))
  **  ((( &( "a" ) )) # Int  |-> (Znth ((i - 1 ) - 0 ) (fib4_prefix_z (i)) 0))
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "f" ) )) # Ptr  |-> f)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_seg f i 100 )
|--
  “ (4 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 4) ”
.

Definition fib4_safety_wit_20 := 
(
forall (n0: Z) (f: Z) (i: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 35)) (PreH3 : (problem_46_pre_z n0 )) (PreH4 : (fib4_safe_z n0 )) (PreH5 : (f <> 0)) (PreH6 : (4 <= i)) (PreH7 : (i <= n0)) (PreH8 : ((fib4_fill_len_z (n0) (i)) = i)) ,
  (IntArray.seg f 0 i (fib4_prefix_z (i)) )
  **  ((( &( "d" ) )) # Int  |-> (Znth ((i - 4 ) - 0 ) (fib4_prefix_z (i)) 0))
  **  ((( &( "c" ) )) # Int  |-> (Znth ((i - 3 ) - 0 ) (fib4_prefix_z (i)) 0))
  **  ((( &( "b" ) )) # Int  |-> (Znth ((i - 2 ) - 0 ) (fib4_prefix_z (i)) 0))
  **  ((( &( "a" ) )) # Int  |-> (Znth ((i - 1 ) - 0 ) (fib4_prefix_z (i)) 0))
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "f" ) )) # Ptr  |-> f)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_seg f i 100 )
|--
  “ (((((Znth ((i - 1 ) - 0 ) (fib4_prefix_z (i)) 0) + (Znth ((i - 2 ) - 0 ) (fib4_prefix_z (i)) 0) ) + (Znth ((i - 3 ) - 0 ) (fib4_prefix_z (i)) 0) ) + (Znth ((i - 4 ) - 0 ) (fib4_prefix_z (i)) 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((((Znth ((i - 1 ) - 0 ) (fib4_prefix_z (i)) 0) + (Znth ((i - 2 ) - 0 ) (fib4_prefix_z (i)) 0) ) + (Znth ((i - 3 ) - 0 ) (fib4_prefix_z (i)) 0) ) + (Znth ((i - 4 ) - 0 ) (fib4_prefix_z (i)) 0) )) ”
) \/
(
forall (n0: Z) (f: Z) (i: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 35)) (PreH3 : (problem_46_pre_z n0 )) (PreH4 : (fib4_safe_z n0 )) (PreH5 : (f <> 0)) (PreH6 : (4 <= i)) (PreH7 : (i <= n0)) (PreH8 : ((fib4_fill_len_z (n0) (i)) = i)) ,
  (IntArray.seg f 0 i (fib4_prefix_z (i)) )
  **  ((( &( "d" ) )) # Int  |-> (Znth ((i - 4 ) - 0 ) (fib4_prefix_z (i)) 0))
  **  ((( &( "c" ) )) # Int  |-> (Znth ((i - 3 ) - 0 ) (fib4_prefix_z (i)) 0))
  **  ((( &( "b" ) )) # Int  |-> (Znth ((i - 2 ) - 0 ) (fib4_prefix_z (i)) 0))
  **  ((( &( "a" ) )) # Int  |-> (Znth ((i - 1 ) - 0 ) (fib4_prefix_z (i)) 0))
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "f" ) )) # Ptr  |-> f)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_seg f i 100 )
|--
  “ (((((Znth ((i - 1 ) - 0 ) (fib4_prefix_z (i)) 0) + (Znth ((i - 2 ) - 0 ) (fib4_prefix_z (i)) 0) ) + (Znth ((i - 3 ) - 0 ) (fib4_prefix_z (i)) 0) ) + (Znth ((i - 4 ) - 0 ) (fib4_prefix_z (i)) 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((((Znth ((i - 1 ) - 0 ) (fib4_prefix_z (i)) 0) + (Znth ((i - 2 ) - 0 ) (fib4_prefix_z (i)) 0) ) + (Znth ((i - 3 ) - 0 ) (fib4_prefix_z (i)) 0) ) + (Znth ((i - 4 ) - 0 ) (fib4_prefix_z (i)) 0) )) ”
).

Definition fib4_safety_wit_20_split_goal_1 := 
forall (n0: Z) (f: Z) (i: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 35)) (PreH3 : (problem_46_pre_z n0 )) (PreH4 : (fib4_safe_z n0 )) (PreH5 : (f <> 0)) (PreH6 : (4 <= i)) (PreH7 : (i <= n0)) (PreH8 : ((fib4_fill_len_z (n0) (i)) = i)) ,
  (IntArray.seg f 0 i (fib4_prefix_z (i)) )
  **  ((( &( "d" ) )) # Int  |-> (Znth ((i - 4 ) - 0 ) (fib4_prefix_z (i)) 0))
  **  ((( &( "c" ) )) # Int  |-> (Znth ((i - 3 ) - 0 ) (fib4_prefix_z (i)) 0))
  **  ((( &( "b" ) )) # Int  |-> (Znth ((i - 2 ) - 0 ) (fib4_prefix_z (i)) 0))
  **  ((( &( "a" ) )) # Int  |-> (Znth ((i - 1 ) - 0 ) (fib4_prefix_z (i)) 0))
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "f" ) )) # Ptr  |-> f)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_seg f i 100 )
|--
  “ (((((Znth ((i - 1 ) - 0 ) (fib4_prefix_z (i)) 0) + (Znth ((i - 2 ) - 0 ) (fib4_prefix_z (i)) 0) ) + (Znth ((i - 3 ) - 0 ) (fib4_prefix_z (i)) 0) ) + (Znth ((i - 4 ) - 0 ) (fib4_prefix_z (i)) 0) ) <= INT_MAX) ”
.

Definition fib4_safety_wit_20_split_goal_2 := 
forall (n0: Z) (f: Z) (i: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 35)) (PreH3 : (problem_46_pre_z n0 )) (PreH4 : (fib4_safe_z n0 )) (PreH5 : (f <> 0)) (PreH6 : (4 <= i)) (PreH7 : (i <= n0)) (PreH8 : ((fib4_fill_len_z (n0) (i)) = i)) ,
  (IntArray.seg f 0 i (fib4_prefix_z (i)) )
  **  ((( &( "d" ) )) # Int  |-> (Znth ((i - 4 ) - 0 ) (fib4_prefix_z (i)) 0))
  **  ((( &( "c" ) )) # Int  |-> (Znth ((i - 3 ) - 0 ) (fib4_prefix_z (i)) 0))
  **  ((( &( "b" ) )) # Int  |-> (Znth ((i - 2 ) - 0 ) (fib4_prefix_z (i)) 0))
  **  ((( &( "a" ) )) # Int  |-> (Znth ((i - 1 ) - 0 ) (fib4_prefix_z (i)) 0))
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "f" ) )) # Ptr  |-> f)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_seg f i 100 )
|--
  “ ((INT_MIN) <= ((((Znth ((i - 1 ) - 0 ) (fib4_prefix_z (i)) 0) + (Znth ((i - 2 ) - 0 ) (fib4_prefix_z (i)) 0) ) + (Znth ((i - 3 ) - 0 ) (fib4_prefix_z (i)) 0) ) + (Znth ((i - 4 ) - 0 ) (fib4_prefix_z (i)) 0) )) ”
.

Definition fib4_safety_wit_21 := 
(
forall (n0: Z) (f: Z) (i: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 35)) (PreH3 : (problem_46_pre_z n0 )) (PreH4 : (fib4_safe_z n0 )) (PreH5 : (f <> 0)) (PreH6 : (4 <= i)) (PreH7 : (i <= n0)) (PreH8 : ((fib4_fill_len_z (n0) (i)) = i)) ,
  (IntArray.seg f 0 i (fib4_prefix_z (i)) )
  **  ((( &( "d" ) )) # Int  |-> (Znth ((i - 4 ) - 0 ) (fib4_prefix_z (i)) 0))
  **  ((( &( "c" ) )) # Int  |-> (Znth ((i - 3 ) - 0 ) (fib4_prefix_z (i)) 0))
  **  ((( &( "b" ) )) # Int  |-> (Znth ((i - 2 ) - 0 ) (fib4_prefix_z (i)) 0))
  **  ((( &( "a" ) )) # Int  |-> (Znth ((i - 1 ) - 0 ) (fib4_prefix_z (i)) 0))
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "f" ) )) # Ptr  |-> f)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_seg f i 100 )
|--
  “ ((((Znth ((i - 1 ) - 0 ) (fib4_prefix_z (i)) 0) + (Znth ((i - 2 ) - 0 ) (fib4_prefix_z (i)) 0) ) + (Znth ((i - 3 ) - 0 ) (fib4_prefix_z (i)) 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((Znth ((i - 1 ) - 0 ) (fib4_prefix_z (i)) 0) + (Znth ((i - 2 ) - 0 ) (fib4_prefix_z (i)) 0) ) + (Znth ((i - 3 ) - 0 ) (fib4_prefix_z (i)) 0) )) ”
) \/
(
forall (n0: Z) (f: Z) (i: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 35)) (PreH3 : (problem_46_pre_z n0 )) (PreH4 : (fib4_safe_z n0 )) (PreH5 : (f <> 0)) (PreH6 : (4 <= i)) (PreH7 : (i <= n0)) (PreH8 : ((fib4_fill_len_z (n0) (i)) = i)) ,
  (IntArray.seg f 0 i (fib4_prefix_z (i)) )
  **  ((( &( "d" ) )) # Int  |-> (Znth ((i - 4 ) - 0 ) (fib4_prefix_z (i)) 0))
  **  ((( &( "c" ) )) # Int  |-> (Znth ((i - 3 ) - 0 ) (fib4_prefix_z (i)) 0))
  **  ((( &( "b" ) )) # Int  |-> (Znth ((i - 2 ) - 0 ) (fib4_prefix_z (i)) 0))
  **  ((( &( "a" ) )) # Int  |-> (Znth ((i - 1 ) - 0 ) (fib4_prefix_z (i)) 0))
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "f" ) )) # Ptr  |-> f)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_seg f i 100 )
|--
  “ ((((Znth ((i - 1 ) - 0 ) (fib4_prefix_z (i)) 0) + (Znth ((i - 2 ) - 0 ) (fib4_prefix_z (i)) 0) ) + (Znth ((i - 3 ) - 0 ) (fib4_prefix_z (i)) 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((Znth ((i - 1 ) - 0 ) (fib4_prefix_z (i)) 0) + (Znth ((i - 2 ) - 0 ) (fib4_prefix_z (i)) 0) ) + (Znth ((i - 3 ) - 0 ) (fib4_prefix_z (i)) 0) )) ”
).

Definition fib4_safety_wit_21_split_goal_1 := 
forall (n0: Z) (f: Z) (i: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 35)) (PreH3 : (problem_46_pre_z n0 )) (PreH4 : (fib4_safe_z n0 )) (PreH5 : (f <> 0)) (PreH6 : (4 <= i)) (PreH7 : (i <= n0)) (PreH8 : ((fib4_fill_len_z (n0) (i)) = i)) ,
  (IntArray.seg f 0 i (fib4_prefix_z (i)) )
  **  ((( &( "d" ) )) # Int  |-> (Znth ((i - 4 ) - 0 ) (fib4_prefix_z (i)) 0))
  **  ((( &( "c" ) )) # Int  |-> (Znth ((i - 3 ) - 0 ) (fib4_prefix_z (i)) 0))
  **  ((( &( "b" ) )) # Int  |-> (Znth ((i - 2 ) - 0 ) (fib4_prefix_z (i)) 0))
  **  ((( &( "a" ) )) # Int  |-> (Znth ((i - 1 ) - 0 ) (fib4_prefix_z (i)) 0))
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "f" ) )) # Ptr  |-> f)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_seg f i 100 )
|--
  “ ((((Znth ((i - 1 ) - 0 ) (fib4_prefix_z (i)) 0) + (Znth ((i - 2 ) - 0 ) (fib4_prefix_z (i)) 0) ) + (Znth ((i - 3 ) - 0 ) (fib4_prefix_z (i)) 0) ) <= INT_MAX) ”
.

Definition fib4_safety_wit_21_split_goal_2 := 
forall (n0: Z) (f: Z) (i: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 35)) (PreH3 : (problem_46_pre_z n0 )) (PreH4 : (fib4_safe_z n0 )) (PreH5 : (f <> 0)) (PreH6 : (4 <= i)) (PreH7 : (i <= n0)) (PreH8 : ((fib4_fill_len_z (n0) (i)) = i)) ,
  (IntArray.seg f 0 i (fib4_prefix_z (i)) )
  **  ((( &( "d" ) )) # Int  |-> (Znth ((i - 4 ) - 0 ) (fib4_prefix_z (i)) 0))
  **  ((( &( "c" ) )) # Int  |-> (Znth ((i - 3 ) - 0 ) (fib4_prefix_z (i)) 0))
  **  ((( &( "b" ) )) # Int  |-> (Znth ((i - 2 ) - 0 ) (fib4_prefix_z (i)) 0))
  **  ((( &( "a" ) )) # Int  |-> (Znth ((i - 1 ) - 0 ) (fib4_prefix_z (i)) 0))
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "f" ) )) # Ptr  |-> f)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_seg f i 100 )
|--
  “ ((INT_MIN) <= (((Znth ((i - 1 ) - 0 ) (fib4_prefix_z (i)) 0) + (Znth ((i - 2 ) - 0 ) (fib4_prefix_z (i)) 0) ) + (Znth ((i - 3 ) - 0 ) (fib4_prefix_z (i)) 0) )) ”
.

Definition fib4_safety_wit_22 := 
(
forall (n0: Z) (f: Z) (i: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 35)) (PreH3 : (problem_46_pre_z n0 )) (PreH4 : (fib4_safe_z n0 )) (PreH5 : (f <> 0)) (PreH6 : (4 <= i)) (PreH7 : (i <= n0)) (PreH8 : ((fib4_fill_len_z (n0) (i)) = i)) ,
  (IntArray.seg f 0 i (fib4_prefix_z (i)) )
  **  ((( &( "d" ) )) # Int  |-> (Znth ((i - 4 ) - 0 ) (fib4_prefix_z (i)) 0))
  **  ((( &( "c" ) )) # Int  |-> (Znth ((i - 3 ) - 0 ) (fib4_prefix_z (i)) 0))
  **  ((( &( "b" ) )) # Int  |-> (Znth ((i - 2 ) - 0 ) (fib4_prefix_z (i)) 0))
  **  ((( &( "a" ) )) # Int  |-> (Znth ((i - 1 ) - 0 ) (fib4_prefix_z (i)) 0))
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "f" ) )) # Ptr  |-> f)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_seg f i 100 )
|--
  “ (((Znth ((i - 1 ) - 0 ) (fib4_prefix_z (i)) 0) + (Znth ((i - 2 ) - 0 ) (fib4_prefix_z (i)) 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth ((i - 1 ) - 0 ) (fib4_prefix_z (i)) 0) + (Znth ((i - 2 ) - 0 ) (fib4_prefix_z (i)) 0) )) ”
) \/
(
forall (n0: Z) (f: Z) (i: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 35)) (PreH3 : (problem_46_pre_z n0 )) (PreH4 : (fib4_safe_z n0 )) (PreH5 : (f <> 0)) (PreH6 : (4 <= i)) (PreH7 : (i <= n0)) (PreH8 : ((fib4_fill_len_z (n0) (i)) = i)) ,
  (IntArray.seg f 0 i (fib4_prefix_z (i)) )
  **  ((( &( "d" ) )) # Int  |-> (Znth ((i - 4 ) - 0 ) (fib4_prefix_z (i)) 0))
  **  ((( &( "c" ) )) # Int  |-> (Znth ((i - 3 ) - 0 ) (fib4_prefix_z (i)) 0))
  **  ((( &( "b" ) )) # Int  |-> (Znth ((i - 2 ) - 0 ) (fib4_prefix_z (i)) 0))
  **  ((( &( "a" ) )) # Int  |-> (Znth ((i - 1 ) - 0 ) (fib4_prefix_z (i)) 0))
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "f" ) )) # Ptr  |-> f)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_seg f i 100 )
|--
  “ (((Znth ((i - 1 ) - 0 ) (fib4_prefix_z (i)) 0) + (Znth ((i - 2 ) - 0 ) (fib4_prefix_z (i)) 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth ((i - 1 ) - 0 ) (fib4_prefix_z (i)) 0) + (Znth ((i - 2 ) - 0 ) (fib4_prefix_z (i)) 0) )) ”
).

Definition fib4_safety_wit_22_split_goal_1 := 
forall (n0: Z) (f: Z) (i: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 35)) (PreH3 : (problem_46_pre_z n0 )) (PreH4 : (fib4_safe_z n0 )) (PreH5 : (f <> 0)) (PreH6 : (4 <= i)) (PreH7 : (i <= n0)) (PreH8 : ((fib4_fill_len_z (n0) (i)) = i)) ,
  (IntArray.seg f 0 i (fib4_prefix_z (i)) )
  **  ((( &( "d" ) )) # Int  |-> (Znth ((i - 4 ) - 0 ) (fib4_prefix_z (i)) 0))
  **  ((( &( "c" ) )) # Int  |-> (Znth ((i - 3 ) - 0 ) (fib4_prefix_z (i)) 0))
  **  ((( &( "b" ) )) # Int  |-> (Znth ((i - 2 ) - 0 ) (fib4_prefix_z (i)) 0))
  **  ((( &( "a" ) )) # Int  |-> (Znth ((i - 1 ) - 0 ) (fib4_prefix_z (i)) 0))
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "f" ) )) # Ptr  |-> f)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_seg f i 100 )
|--
  “ (((Znth ((i - 1 ) - 0 ) (fib4_prefix_z (i)) 0) + (Znth ((i - 2 ) - 0 ) (fib4_prefix_z (i)) 0) ) <= INT_MAX) ”
.

Definition fib4_safety_wit_22_split_goal_2 := 
forall (n0: Z) (f: Z) (i: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 35)) (PreH3 : (problem_46_pre_z n0 )) (PreH4 : (fib4_safe_z n0 )) (PreH5 : (f <> 0)) (PreH6 : (4 <= i)) (PreH7 : (i <= n0)) (PreH8 : ((fib4_fill_len_z (n0) (i)) = i)) ,
  (IntArray.seg f 0 i (fib4_prefix_z (i)) )
  **  ((( &( "d" ) )) # Int  |-> (Znth ((i - 4 ) - 0 ) (fib4_prefix_z (i)) 0))
  **  ((( &( "c" ) )) # Int  |-> (Znth ((i - 3 ) - 0 ) (fib4_prefix_z (i)) 0))
  **  ((( &( "b" ) )) # Int  |-> (Znth ((i - 2 ) - 0 ) (fib4_prefix_z (i)) 0))
  **  ((( &( "a" ) )) # Int  |-> (Znth ((i - 1 ) - 0 ) (fib4_prefix_z (i)) 0))
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "f" ) )) # Ptr  |-> f)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_seg f i 100 )
|--
  “ ((INT_MIN) <= ((Znth ((i - 1 ) - 0 ) (fib4_prefix_z (i)) 0) + (Znth ((i - 2 ) - 0 ) (fib4_prefix_z (i)) 0) )) ”
.

Definition fib4_safety_wit_23 := 
forall (n0: Z) (f: Z) (i: Z) (a: Z) (b: Z) (c: Z) (d: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 35)) (PreH3 : (problem_46_pre_z n0 )) (PreH4 : (fib4_safe_z n0 )) (PreH5 : (f <> 0)) (PreH6 : (4 <= i)) (PreH7 : (i <= n0)) (PreH8 : (a = (fib4_z ((i - 1 ))))) (PreH9 : (b = (fib4_z ((i - 2 ))))) (PreH10 : (c = (fib4_z ((i - 3 ))))) (PreH11 : (d = (fib4_z ((i - 4 ))))) (PreH12 : ((fib4_z (i)) = (((a + b ) + c ) + d ))) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "f" ) )) # Ptr  |-> f)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.seg f 0 (i + 1 ) (fib4_prefix_z ((i + 1 ))) )
  **  (IntArray.undef_seg f (i + 1 ) 100 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition fib4_safety_wit_24 := 
forall (n0: Z) (f: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 35)) (PreH3 : (problem_46_pre_z n0 )) (PreH4 : (fib4_safe_z n0 )) (PreH5 : (f <> 0)) ,
  ((( &( "filled" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "f" ) )) # Ptr  |-> f)
  **  (IntArray.seg f 0 (fib4_fill_len_z (n0) ((n0 + 1 ))) (fib4_prefix_z ((fib4_fill_len_z (n0) ((n0 + 1 ))))) )
  **  (IntArray.undef_seg f (fib4_fill_len_z (n0) ((n0 + 1 ))) 100 )
|--
  “ ((n0 + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n0 + 1 )) ”
.

Definition fib4_safety_wit_25 := 
forall (n0: Z) (f: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 35)) (PreH3 : (problem_46_pre_z n0 )) (PreH4 : (fib4_safe_z n0 )) (PreH5 : (f <> 0)) ,
  ((( &( "filled" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "f" ) )) # Ptr  |-> f)
  **  (IntArray.seg f 0 (fib4_fill_len_z (n0) ((n0 + 1 ))) (fib4_prefix_z ((fib4_fill_len_z (n0) ((n0 + 1 ))))) )
  **  (IntArray.undef_seg f (fib4_fill_len_z (n0) ((n0 + 1 ))) 100 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition fib4_safety_wit_26 := 
forall (n0: Z) (f: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 35)) (PreH3 : (problem_46_pre_z n0 )) (PreH4 : (fib4_safe_z n0 )) (PreH5 : (f <> 0)) ,
  ((( &( "filled" ) )) # Int  |-> (n0 + 1 ))
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "f" ) )) # Ptr  |-> f)
  **  (IntArray.seg f 0 (fib4_fill_len_z (n0) ((n0 + 1 ))) (fib4_prefix_z ((fib4_fill_len_z (n0) ((n0 + 1 ))))) )
  **  (IntArray.undef_seg f (fib4_fill_len_z (n0) ((n0 + 1 ))) 100 )
|--
  “ (4 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 4) ”
.

Definition fib4_safety_wit_27 := 
forall (n0: Z) (f: Z) (PreH1 : (n0 < 4)) (PreH2 : (0 <= n0)) (PreH3 : (n0 <= 35)) (PreH4 : (problem_46_pre_z n0 )) (PreH5 : (fib4_safe_z n0 )) (PreH6 : (f <> 0)) ,
  ((( &( "filled" ) )) # Int  |-> (n0 + 1 ))
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "f" ) )) # Ptr  |-> f)
  **  (IntArray.seg f 0 (fib4_fill_len_z (n0) ((n0 + 1 ))) (fib4_prefix_z ((fib4_fill_len_z (n0) ((n0 + 1 ))))) )
  **  (IntArray.undef_seg f (fib4_fill_len_z (n0) ((n0 + 1 ))) 100 )
|--
  “ (4 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 4) ”
.

Definition fib4_safety_wit_28 := 
forall (n0: Z) (result: Z) (filled: Z) (f: Z) (PreH1 : (result = (fib4_z (n0)))) (PreH2 : (filled = (fib4_fill_len_z (n0) ((n0 + 1 ))))) (PreH3 : (n0 < filled)) (PreH4 : (0 <= n0)) (PreH5 : (n0 <= 35)) (PreH6 : (problem_46_pre_z n0 )) (PreH7 : (fib4_safe_z n0 )) (PreH8 : (f <> 0)) (PreH9 : (filled <= 100)) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "result" ) )) # Int  |-> result)
  **  ((( &( "filled" ) )) # Int  |-> filled)
  **  ((( &( "f" ) )) # Ptr  |-> f)
  **  (IntArray.seg f 0 filled (fib4_prefix_z (filled)) )
  **  (IntArray.undef_seg f filled 100 )
|--
  “ (100 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 100) ”
.

Definition fib4_entail_wit_1 := 
(
forall (n_pre: Z) (n0: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (n_pre = n0)) (PreH3 : (0 <= n0)) (PreH4 : (n0 <= 35)) (PreH5 : (problem_46_pre_z n0 )) (PreH6 : (fib4_safe_z n0 )) ,
  (((retval + (0 * sizeof(INT) ) )) # Int  |-> 0)
  **  (IntArray.undef_seg retval 1 100 )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (0 <= n0) ” 
  &&  “ (n0 <= 35) ” 
  &&  “ (problem_46_pre_z n0 ) ” 
  &&  “ (fib4_safe_z n0 ) ” 
  &&  “ (retval <> 0) ”
  &&  ((( &( "n" ) )) # Int  |-> n0)
  **  (IntArray.seg retval 0 1 (cons (0) ((@nil Z))) )
  **  (IntArray.undef_seg retval 1 100 )
) \/
(
forall (n_pre: Z) (n0: Z) (retval: Z) (PreH1 : (0 <= INT_MAX)) (PreH2 : (0 >= INT_MIN)) (PreH3 : (retval <> 0)) (PreH4 : (n_pre = n0)) (PreH5 : (0 <= n0)) (PreH6 : (n0 <= 35)) (PreH7 : (problem_46_pre_z n0 )) (PreH8 : (fib4_safe_z n0 )) ,
  (((retval + (0 * sizeof(INT) ) )) # Int  |-> 0)
|--
  (IntArray.seg retval 0 1 (cons (0) ((@nil Z))) )
).

Definition fib4_entail_wit_1_split_goal_spatial := 
forall (n_pre: Z) (n0: Z) (retval: Z) (PreH1 : (0 <= INT_MAX)) (PreH2 : (0 >= INT_MIN)) (PreH3 : (retval <> 0)) (PreH4 : (n_pre = n0)) (PreH5 : (0 <= n0)) (PreH6 : (n0 <= 35)) (PreH7 : (problem_46_pre_z n0 )) (PreH8 : (fib4_safe_z n0 )) ,
  (((retval + (0 * sizeof(INT) ) )) # Int  |-> 0)
|--
  (IntArray.seg retval 0 1 (cons (0) ((@nil Z))) )
.

Definition fib4_entail_wit_2 := 
(
forall (n0: Z) (f: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 35)) (PreH3 : (problem_46_pre_z n0 )) (PreH4 : (fib4_safe_z n0 )) (PreH5 : (f <> 0)) ,
  (IntArray.seg f 0 (1 + 1 ) (app ((cons (0) ((@nil Z)))) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg f (1 + 1 ) 100 )
|--
  “ (0 <= n0) ” 
  &&  “ (n0 <= 35) ” 
  &&  “ (problem_46_pre_z n0 ) ” 
  &&  “ (fib4_safe_z n0 ) ” 
  &&  “ (f <> 0) ”
  &&  (IntArray.seg f 0 2 (cons (0) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg f 2 100 )
) \/
(
forall (n0: Z) (f: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 35)) (PreH3 : (problem_46_pre_z n0 )) (PreH4 : (fib4_safe_z n0 )) (PreH5 : (f <> 0)) ,
  (IntArray.seg f 0 (1 + 1 ) (app ((cons (0) ((@nil Z)))) ((cons (0) ((@nil Z))))) )
|--
  (IntArray.seg f 0 2 (cons (0) ((cons (0) ((@nil Z))))) )
).

Definition fib4_entail_wit_2_split_goal_spatial := 
forall (n0: Z) (f: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 35)) (PreH3 : (problem_46_pre_z n0 )) (PreH4 : (fib4_safe_z n0 )) (PreH5 : (f <> 0)) ,
  (IntArray.seg f 0 (1 + 1 ) (app ((cons (0) ((@nil Z)))) ((cons (0) ((@nil Z))))) )
|--
  (IntArray.seg f 0 2 (cons (0) ((cons (0) ((@nil Z))))) )
.

Definition fib4_entail_wit_3 := 
(
forall (n0: Z) (f: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 35)) (PreH3 : (problem_46_pre_z n0 )) (PreH4 : (fib4_safe_z n0 )) (PreH5 : (f <> 0)) ,
  (IntArray.seg f 0 (2 + 1 ) (app ((cons (0) ((cons (0) ((@nil Z)))))) ((cons (2) ((@nil Z))))) )
  **  (IntArray.undef_seg f (2 + 1 ) 100 )
|--
  “ (0 <= n0) ” 
  &&  “ (n0 <= 35) ” 
  &&  “ (problem_46_pre_z n0 ) ” 
  &&  “ (fib4_safe_z n0 ) ” 
  &&  “ (f <> 0) ”
  &&  (IntArray.seg f 0 3 (cons (0) ((cons (0) ((cons (2) ((@nil Z))))))) )
  **  (IntArray.undef_seg f 3 100 )
) \/
(
forall (n0: Z) (f: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 35)) (PreH3 : (problem_46_pre_z n0 )) (PreH4 : (fib4_safe_z n0 )) (PreH5 : (f <> 0)) ,
  (IntArray.seg f 0 (2 + 1 ) (app ((cons (0) ((cons (0) ((@nil Z)))))) ((cons (2) ((@nil Z))))) )
|--
  (IntArray.seg f 0 3 (cons (0) ((cons (0) ((cons (2) ((@nil Z))))))) )
).

Definition fib4_entail_wit_3_split_goal_spatial := 
forall (n0: Z) (f: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 35)) (PreH3 : (problem_46_pre_z n0 )) (PreH4 : (fib4_safe_z n0 )) (PreH5 : (f <> 0)) ,
  (IntArray.seg f 0 (2 + 1 ) (app ((cons (0) ((cons (0) ((@nil Z)))))) ((cons (2) ((@nil Z))))) )
|--
  (IntArray.seg f 0 3 (cons (0) ((cons (0) ((cons (2) ((@nil Z))))))) )
.

Definition fib4_entail_wit_4 := 
(
forall (n0: Z) (f: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 35)) (PreH3 : (problem_46_pre_z n0 )) (PreH4 : (fib4_safe_z n0 )) (PreH5 : (f <> 0)) ,
  (IntArray.seg f 0 (3 + 1 ) (app ((cons (0) ((cons (0) ((cons (2) ((@nil Z)))))))) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg f (3 + 1 ) 100 )
|--
  “ (0 <= n0) ” 
  &&  “ (n0 <= 35) ” 
  &&  “ (problem_46_pre_z n0 ) ” 
  &&  “ (fib4_safe_z n0 ) ” 
  &&  “ (f <> 0) ”
  &&  (IntArray.seg f 0 4 (fib4_prefix_z (4)) )
  **  (IntArray.undef_seg f 4 100 )
) \/
(
forall (n0: Z) (f: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 35)) (PreH3 : (problem_46_pre_z n0 )) (PreH4 : (fib4_safe_z n0 )) (PreH5 : (f <> 0)) ,
  (IntArray.seg f 0 (3 + 1 ) (app ((cons (0) ((cons (0) ((cons (2) ((@nil Z)))))))) ((cons (0) ((@nil Z))))) )
|--
  (IntArray.seg f 0 4 (fib4_prefix_z (4)) )
).

Definition fib4_entail_wit_4_split_goal_spatial := 
forall (n0: Z) (f: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 35)) (PreH3 : (problem_46_pre_z n0 )) (PreH4 : (fib4_safe_z n0 )) (PreH5 : (f <> 0)) ,
  (IntArray.seg f 0 (3 + 1 ) (app ((cons (0) ((cons (0) ((cons (2) ((@nil Z)))))))) ((cons (0) ((@nil Z))))) )
|--
  (IntArray.seg f 0 4 (fib4_prefix_z (4)) )
.

Definition fib4_entail_wit_5 := 
forall (n0: Z) (f: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 35)) (PreH3 : (problem_46_pre_z n0 )) (PreH4 : (fib4_safe_z n0 )) (PreH5 : (f <> 0)) ,
  (IntArray.seg f 0 4 (fib4_prefix_z (4)) )
  **  (IntArray.undef_seg f 4 100 )
|--
  (“ (0 <= n0) ” 
  &&  “ (n0 <= 35) ” 
  &&  “ (problem_46_pre_z n0 ) ” 
  &&  “ (fib4_safe_z n0 ) ” 
  &&  “ (f <> 0) ” 
  &&  “ (4 <= 4) ” 
  &&  “ (4 <= 36) ” 
  &&  “ (n0 < 4) ” 
  &&  “ (4 = 4) ”
  &&  (IntArray.seg f 0 (fib4_fill_len_z (n0) (4)) (fib4_prefix_z ((fib4_fill_len_z (n0) (4)))) )
  **  (IntArray.undef_seg f (fib4_fill_len_z (n0) (4)) 100 ))
  ||
  (“ (0 <= n0) ” 
  &&  “ (n0 <= 35) ” 
  &&  “ (problem_46_pre_z n0 ) ” 
  &&  “ (fib4_safe_z n0 ) ” 
  &&  “ (f <> 0) ” 
  &&  “ (4 <= 4) ” 
  &&  “ (4 <= 36) ” 
  &&  “ (4 <= n0) ” 
  &&  “ (4 <= (n0 + 1 )) ”
  &&  (IntArray.seg f 0 (fib4_fill_len_z (n0) (4)) (fib4_prefix_z ((fib4_fill_len_z (n0) (4)))) )
  **  (IntArray.undef_seg f (fib4_fill_len_z (n0) (4)) 100 ))
.

Definition fib4_entail_wit_6 := 
(
forall (n0: Z) (i: Z) (f: Z) (PreH1 : (i <= n0)) (PreH2 : (0 <= n0)) (PreH3 : (n0 <= 35)) (PreH4 : (problem_46_pre_z n0 )) (PreH5 : (fib4_safe_z n0 )) (PreH6 : (f <> 0)) (PreH7 : (4 <= i)) (PreH8 : (i <= 36)) (PreH9 : (4 <= n0)) (PreH10 : (i <= (n0 + 1 ))) ,
  (IntArray.seg f 0 (fib4_fill_len_z (n0) (i)) (fib4_prefix_z ((fib4_fill_len_z (n0) (i)))) )
  **  (IntArray.undef_seg f (fib4_fill_len_z (n0) (i)) 100 )
|--
  “ (0 <= n0) ” 
  &&  “ (n0 <= 35) ” 
  &&  “ (problem_46_pre_z n0 ) ” 
  &&  “ (fib4_safe_z n0 ) ” 
  &&  “ (f <> 0) ” 
  &&  “ (4 <= i) ” 
  &&  “ (i <= n0) ” 
  &&  “ ((fib4_fill_len_z (n0) (i)) = i) ”
  &&  (IntArray.seg f 0 i (fib4_prefix_z (i)) )
  **  (IntArray.undef_seg f i 100 )
) \/
(
forall (n0: Z) (i: Z) (f: Z) (PreH1 : (i <= n0)) (PreH2 : (0 <= n0)) (PreH3 : (n0 <= 35)) (PreH4 : (problem_46_pre_z n0 )) (PreH5 : (fib4_safe_z n0 )) (PreH6 : (f <> 0)) (PreH7 : (4 <= i)) (PreH8 : (i <= 36)) (PreH9 : (4 <= n0)) (PreH10 : (i <= (n0 + 1 ))) ,
  (IntArray.seg f 0 (fib4_fill_len_z (n0) (i)) (fib4_prefix_z ((fib4_fill_len_z (n0) (i)))) )
  **  (IntArray.undef_seg f (fib4_fill_len_z (n0) (i)) 100 )
|--
  “ ((fib4_fill_len_z (n0) (i)) = i) ”
  &&  (IntArray.seg f 0 i (fib4_prefix_z (i)) )
  **  (IntArray.undef_seg f i 100 )
).

Definition fib4_entail_wit_6_split_goal_1 := 
forall (n0: Z) (i: Z) (f: Z) (PreH1 : (i <= n0)) (PreH2 : (0 <= n0)) (PreH3 : (n0 <= 35)) (PreH4 : (problem_46_pre_z n0 )) (PreH5 : (fib4_safe_z n0 )) (PreH6 : (f <> 0)) (PreH7 : (4 <= i)) (PreH8 : (i <= 36)) (PreH9 : (4 <= n0)) (PreH10 : (i <= (n0 + 1 ))) ,
  (IntArray.seg f 0 (fib4_fill_len_z (n0) (i)) (fib4_prefix_z ((fib4_fill_len_z (n0) (i)))) )
  **  (IntArray.undef_seg f (fib4_fill_len_z (n0) (i)) 100 )
|--
  “ ((fib4_fill_len_z (n0) (i)) = i) ”
.

Definition fib4_entail_wit_6_split_goal_spatial := 
forall (n0: Z) (i: Z) (f: Z) (PreH1 : (i <= n0)) (PreH2 : (0 <= n0)) (PreH3 : (n0 <= 35)) (PreH4 : (problem_46_pre_z n0 )) (PreH5 : (fib4_safe_z n0 )) (PreH6 : (f <> 0)) (PreH7 : (4 <= i)) (PreH8 : (i <= 36)) (PreH9 : (4 <= n0)) (PreH10 : (i <= (n0 + 1 ))) ,
  (IntArray.seg f 0 (fib4_fill_len_z (n0) (i)) (fib4_prefix_z ((fib4_fill_len_z (n0) (i)))) )
  **  (IntArray.undef_seg f (fib4_fill_len_z (n0) (i)) 100 )
|--
  (IntArray.seg f 0 i (fib4_prefix_z (i)) )
  **  (IntArray.undef_seg f i 100 )
.

Definition fib4_entail_wit_7 := 
(
forall (n0: Z) (f: Z) (i: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 35)) (PreH3 : (problem_46_pre_z n0 )) (PreH4 : (fib4_safe_z n0 )) (PreH5 : (f <> 0)) (PreH6 : (4 <= i)) (PreH7 : (i <= n0)) (PreH8 : ((fib4_fill_len_z (n0) (i)) = i)) ,
  (IntArray.seg f 0 (i + 1 ) (app ((fib4_prefix_z (i))) ((cons (((((Znth ((i - 1 ) - 0 ) (fib4_prefix_z (i)) 0) + (Znth ((i - 2 ) - 0 ) (fib4_prefix_z (i)) 0) ) + (Znth ((i - 3 ) - 0 ) (fib4_prefix_z (i)) 0) ) + (Znth ((i - 4 ) - 0 ) (fib4_prefix_z (i)) 0) )) ((@nil Z))))) )
  **  (IntArray.undef_seg f (i + 1 ) 100 )
|--
  “ (0 <= n0) ” 
  &&  “ (n0 <= 35) ” 
  &&  “ (problem_46_pre_z n0 ) ” 
  &&  “ (fib4_safe_z n0 ) ” 
  &&  “ (f <> 0) ” 
  &&  “ (4 <= i) ” 
  &&  “ (i <= n0) ” 
  &&  “ ((Znth ((i - 1 ) - 0 ) (fib4_prefix_z (i)) 0) = (fib4_z ((i - 1 )))) ” 
  &&  “ ((Znth ((i - 2 ) - 0 ) (fib4_prefix_z (i)) 0) = (fib4_z ((i - 2 )))) ” 
  &&  “ ((Znth ((i - 3 ) - 0 ) (fib4_prefix_z (i)) 0) = (fib4_z ((i - 3 )))) ” 
  &&  “ ((Znth ((i - 4 ) - 0 ) (fib4_prefix_z (i)) 0) = (fib4_z ((i - 4 )))) ” 
  &&  “ ((fib4_z (i)) = ((((Znth ((i - 1 ) - 0 ) (fib4_prefix_z (i)) 0) + (Znth ((i - 2 ) - 0 ) (fib4_prefix_z (i)) 0) ) + (Znth ((i - 3 ) - 0 ) (fib4_prefix_z (i)) 0) ) + (Znth ((i - 4 ) - 0 ) (fib4_prefix_z (i)) 0) )) ”
  &&  (IntArray.seg f 0 (i + 1 ) (fib4_prefix_z ((i + 1 ))) )
  **  (IntArray.undef_seg f (i + 1 ) 100 )
) \/
(
forall (n0: Z) (f: Z) (i: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 35)) (PreH3 : (problem_46_pre_z n0 )) (PreH4 : (fib4_safe_z n0 )) (PreH5 : (f <> 0)) (PreH6 : (4 <= i)) (PreH7 : (i <= n0)) (PreH8 : ((fib4_fill_len_z (n0) (i)) = i)) ,
  TT && emp 
|--
  “ ((fib4_z (i)) = ((((Znth ((i - 1 ) - 0 ) (fib4_prefix_z (i)) 0) + (Znth ((i - 2 ) - 0 ) (fib4_prefix_z (i)) 0) ) + (Znth ((i - 3 ) - 0 ) (fib4_prefix_z (i)) 0) ) + (Znth ((i - 4 ) - 0 ) (fib4_prefix_z (i)) 0) )) ” 
  &&  “ ((Znth ((i - 4 ) - 0 ) (fib4_prefix_z (i)) 0) = (fib4_z ((i - 4 )))) ” 
  &&  “ ((Znth ((i - 3 ) - 0 ) (fib4_prefix_z (i)) 0) = (fib4_z ((i - 3 )))) ” 
  &&  “ ((Znth ((i - 2 ) - 0 ) (fib4_prefix_z (i)) 0) = (fib4_z ((i - 2 )))) ” 
  &&  “ ((Znth ((i - 1 ) - 0 ) (fib4_prefix_z (i)) 0) = (fib4_z ((i - 1 )))) ” 
  &&  “ ((app ((fib4_prefix_z (i))) ((cons (((((Znth ((i - 1 ) - 0 ) (fib4_prefix_z (i)) 0) + (Znth ((i - 2 ) - 0 ) (fib4_prefix_z (i)) 0) ) + (Znth ((i - 3 ) - 0 ) (fib4_prefix_z (i)) 0) ) + (Znth ((i - 4 ) - 0 ) (fib4_prefix_z (i)) 0) )) ((@nil Z))))) = (fib4_prefix_z ((i + 1 )))) ”
  &&  emp
).

Definition fib4_entail_wit_7_split_goal_1 := 
forall (n0: Z) (f: Z) (i: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 35)) (PreH3 : (problem_46_pre_z n0 )) (PreH4 : (fib4_safe_z n0 )) (PreH5 : (f <> 0)) (PreH6 : (4 <= i)) (PreH7 : (i <= n0)) (PreH8 : ((fib4_fill_len_z (n0) (i)) = i)) ,
  TT && emp 
|--
  “ ((fib4_z (i)) = ((((Znth ((i - 1 ) - 0 ) (fib4_prefix_z (i)) 0) + (Znth ((i - 2 ) - 0 ) (fib4_prefix_z (i)) 0) ) + (Znth ((i - 3 ) - 0 ) (fib4_prefix_z (i)) 0) ) + (Znth ((i - 4 ) - 0 ) (fib4_prefix_z (i)) 0) )) ”
.

Definition fib4_entail_wit_7_split_goal_2 := 
forall (n0: Z) (f: Z) (i: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 35)) (PreH3 : (problem_46_pre_z n0 )) (PreH4 : (fib4_safe_z n0 )) (PreH5 : (f <> 0)) (PreH6 : (4 <= i)) (PreH7 : (i <= n0)) (PreH8 : ((fib4_fill_len_z (n0) (i)) = i)) ,
  TT && emp 
|--
  “ ((Znth ((i - 4 ) - 0 ) (fib4_prefix_z (i)) 0) = (fib4_z ((i - 4 )))) ”
.

Definition fib4_entail_wit_7_split_goal_3 := 
forall (n0: Z) (f: Z) (i: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 35)) (PreH3 : (problem_46_pre_z n0 )) (PreH4 : (fib4_safe_z n0 )) (PreH5 : (f <> 0)) (PreH6 : (4 <= i)) (PreH7 : (i <= n0)) (PreH8 : ((fib4_fill_len_z (n0) (i)) = i)) ,
  TT && emp 
|--
  “ ((Znth ((i - 3 ) - 0 ) (fib4_prefix_z (i)) 0) = (fib4_z ((i - 3 )))) ”
.

Definition fib4_entail_wit_7_split_goal_4 := 
forall (n0: Z) (f: Z) (i: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 35)) (PreH3 : (problem_46_pre_z n0 )) (PreH4 : (fib4_safe_z n0 )) (PreH5 : (f <> 0)) (PreH6 : (4 <= i)) (PreH7 : (i <= n0)) (PreH8 : ((fib4_fill_len_z (n0) (i)) = i)) ,
  TT && emp 
|--
  “ ((Znth ((i - 2 ) - 0 ) (fib4_prefix_z (i)) 0) = (fib4_z ((i - 2 )))) ”
.

Definition fib4_entail_wit_7_split_goal_5 := 
forall (n0: Z) (f: Z) (i: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 35)) (PreH3 : (problem_46_pre_z n0 )) (PreH4 : (fib4_safe_z n0 )) (PreH5 : (f <> 0)) (PreH6 : (4 <= i)) (PreH7 : (i <= n0)) (PreH8 : ((fib4_fill_len_z (n0) (i)) = i)) ,
  TT && emp 
|--
  “ ((Znth ((i - 1 ) - 0 ) (fib4_prefix_z (i)) 0) = (fib4_z ((i - 1 )))) ”
.

Definition fib4_entail_wit_7_split_goal_6 := 
forall (n0: Z) (f: Z) (i: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 35)) (PreH3 : (problem_46_pre_z n0 )) (PreH4 : (fib4_safe_z n0 )) (PreH5 : (f <> 0)) (PreH6 : (4 <= i)) (PreH7 : (i <= n0)) (PreH8 : ((fib4_fill_len_z (n0) (i)) = i)) ,
  TT && emp 
|--
  “ ((app ((fib4_prefix_z (i))) ((cons (((((Znth ((i - 1 ) - 0 ) (fib4_prefix_z (i)) 0) + (Znth ((i - 2 ) - 0 ) (fib4_prefix_z (i)) 0) ) + (Znth ((i - 3 ) - 0 ) (fib4_prefix_z (i)) 0) ) + (Znth ((i - 4 ) - 0 ) (fib4_prefix_z (i)) 0) )) ((@nil Z))))) = (fib4_prefix_z ((i + 1 )))) ”
.

Definition fib4_entail_wit_8 := 
forall (n0: Z) (f: Z) (i: Z) (a: Z) (b: Z) (c: Z) (d: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 35)) (PreH3 : (problem_46_pre_z n0 )) (PreH4 : (fib4_safe_z n0 )) (PreH5 : (f <> 0)) (PreH6 : (4 <= i)) (PreH7 : (i <= n0)) (PreH8 : (a = (fib4_z ((i - 1 ))))) (PreH9 : (b = (fib4_z ((i - 2 ))))) (PreH10 : (c = (fib4_z ((i - 3 ))))) (PreH11 : (d = (fib4_z ((i - 4 ))))) (PreH12 : ((fib4_z (i)) = (((a + b ) + c ) + d ))) ,
  (IntArray.seg f 0 (i + 1 ) (fib4_prefix_z ((i + 1 ))) )
  **  (IntArray.undef_seg f (i + 1 ) 100 )
|--
  (“ (0 <= n0) ” 
  &&  “ (n0 <= 35) ” 
  &&  “ (problem_46_pre_z n0 ) ” 
  &&  “ (fib4_safe_z n0 ) ” 
  &&  “ (f <> 0) ” 
  &&  “ (4 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= 36) ” 
  &&  “ (n0 < 4) ” 
  &&  “ ((i + 1 ) = 4) ”
  &&  (IntArray.seg f 0 (fib4_fill_len_z (n0) ((i + 1 ))) (fib4_prefix_z ((fib4_fill_len_z (n0) ((i + 1 ))))) )
  **  (IntArray.undef_seg f (fib4_fill_len_z (n0) ((i + 1 ))) 100 ))
  ||
  (“ (0 <= n0) ” 
  &&  “ (n0 <= 35) ” 
  &&  “ (problem_46_pre_z n0 ) ” 
  &&  “ (fib4_safe_z n0 ) ” 
  &&  “ (f <> 0) ” 
  &&  “ (4 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= 36) ” 
  &&  “ (4 <= n0) ” 
  &&  “ ((i + 1 ) <= (n0 + 1 )) ”
  &&  (IntArray.seg f 0 (fib4_fill_len_z (n0) ((i + 1 ))) (fib4_prefix_z ((fib4_fill_len_z (n0) ((i + 1 ))))) )
  **  (IntArray.undef_seg f (fib4_fill_len_z (n0) ((i + 1 ))) 100 ))
.

Definition fib4_entail_wit_9_1 := 
(
forall (n0: Z) (i: Z) (f: Z) (PreH1 : (i > n0)) (PreH2 : (0 <= n0)) (PreH3 : (n0 <= 35)) (PreH4 : (problem_46_pre_z n0 )) (PreH5 : (fib4_safe_z n0 )) (PreH6 : (f <> 0)) (PreH7 : (4 <= i)) (PreH8 : (i <= 36)) (PreH9 : (4 <= n0)) (PreH10 : (i <= (n0 + 1 ))) ,
  (IntArray.seg f 0 (fib4_fill_len_z (n0) (i)) (fib4_prefix_z ((fib4_fill_len_z (n0) (i)))) )
  **  (IntArray.undef_seg f (fib4_fill_len_z (n0) (i)) 100 )
|--
  “ (0 <= n0) ” 
  &&  “ (n0 <= 35) ” 
  &&  “ (problem_46_pre_z n0 ) ” 
  &&  “ (fib4_safe_z n0 ) ” 
  &&  “ (f <> 0) ”
  &&  (IntArray.seg f 0 (fib4_fill_len_z (n0) ((n0 + 1 ))) (fib4_prefix_z ((fib4_fill_len_z (n0) ((n0 + 1 ))))) )
  **  (IntArray.undef_seg f (fib4_fill_len_z (n0) ((n0 + 1 ))) 100 )
) \/
(
forall (n0: Z) (i: Z) (f: Z) (PreH1 : (i > n0)) (PreH2 : (0 <= n0)) (PreH3 : (n0 <= 35)) (PreH4 : (problem_46_pre_z n0 )) (PreH5 : (fib4_safe_z n0 )) (PreH6 : (f <> 0)) (PreH7 : (4 <= i)) (PreH8 : (i <= 36)) (PreH9 : (4 <= n0)) (PreH10 : (i <= (n0 + 1 ))) ,
  (IntArray.seg f 0 (fib4_fill_len_z (n0) (i)) (fib4_prefix_z ((fib4_fill_len_z (n0) (i)))) )
  **  (IntArray.undef_seg f (fib4_fill_len_z (n0) (i)) 100 )
|--
  (IntArray.seg f 0 (fib4_fill_len_z (n0) ((n0 + 1 ))) (fib4_prefix_z ((fib4_fill_len_z (n0) ((n0 + 1 ))))) )
  **  (IntArray.undef_seg f (fib4_fill_len_z (n0) ((n0 + 1 ))) 100 )
).

Definition fib4_entail_wit_9_1_split_goal_spatial := 
forall (n0: Z) (i: Z) (f: Z) (PreH1 : (i > n0)) (PreH2 : (0 <= n0)) (PreH3 : (n0 <= 35)) (PreH4 : (problem_46_pre_z n0 )) (PreH5 : (fib4_safe_z n0 )) (PreH6 : (f <> 0)) (PreH7 : (4 <= i)) (PreH8 : (i <= 36)) (PreH9 : (4 <= n0)) (PreH10 : (i <= (n0 + 1 ))) ,
  (IntArray.seg f 0 (fib4_fill_len_z (n0) (i)) (fib4_prefix_z ((fib4_fill_len_z (n0) (i)))) )
  **  (IntArray.undef_seg f (fib4_fill_len_z (n0) (i)) 100 )
|--
  (IntArray.seg f 0 (fib4_fill_len_z (n0) ((n0 + 1 ))) (fib4_prefix_z ((fib4_fill_len_z (n0) ((n0 + 1 ))))) )
  **  (IntArray.undef_seg f (fib4_fill_len_z (n0) ((n0 + 1 ))) 100 )
.

Definition fib4_entail_wit_9_2 := 
(
forall (n0: Z) (i: Z) (f: Z) (PreH1 : (i > n0)) (PreH2 : (0 <= n0)) (PreH3 : (n0 <= 35)) (PreH4 : (problem_46_pre_z n0 )) (PreH5 : (fib4_safe_z n0 )) (PreH6 : (f <> 0)) (PreH7 : (4 <= i)) (PreH8 : (i <= 36)) (PreH9 : (n0 < 4)) (PreH10 : (i = 4)) ,
  (IntArray.seg f 0 (fib4_fill_len_z (n0) (i)) (fib4_prefix_z ((fib4_fill_len_z (n0) (i)))) )
  **  (IntArray.undef_seg f (fib4_fill_len_z (n0) (i)) 100 )
|--
  “ (0 <= n0) ” 
  &&  “ (n0 <= 35) ” 
  &&  “ (problem_46_pre_z n0 ) ” 
  &&  “ (fib4_safe_z n0 ) ” 
  &&  “ (f <> 0) ”
  &&  (IntArray.seg f 0 (fib4_fill_len_z (n0) ((n0 + 1 ))) (fib4_prefix_z ((fib4_fill_len_z (n0) ((n0 + 1 ))))) )
  **  (IntArray.undef_seg f (fib4_fill_len_z (n0) ((n0 + 1 ))) 100 )
) \/
(
forall (n0: Z) (i: Z) (f: Z) (PreH1 : (i > n0)) (PreH2 : (0 <= n0)) (PreH3 : (n0 <= 35)) (PreH4 : (problem_46_pre_z n0 )) (PreH5 : (fib4_safe_z n0 )) (PreH6 : (f <> 0)) (PreH7 : (4 <= i)) (PreH8 : (i <= 36)) (PreH9 : (n0 < 4)) (PreH10 : (i = 4)) ,
  (IntArray.seg f 0 (fib4_fill_len_z (n0) (i)) (fib4_prefix_z ((fib4_fill_len_z (n0) (i)))) )
  **  (IntArray.undef_seg f (fib4_fill_len_z (n0) (i)) 100 )
|--
  (IntArray.seg f 0 (fib4_fill_len_z (n0) ((n0 + 1 ))) (fib4_prefix_z ((fib4_fill_len_z (n0) ((n0 + 1 ))))) )
  **  (IntArray.undef_seg f (fib4_fill_len_z (n0) ((n0 + 1 ))) 100 )
).

Definition fib4_entail_wit_9_2_split_goal_spatial := 
forall (n0: Z) (i: Z) (f: Z) (PreH1 : (i > n0)) (PreH2 : (0 <= n0)) (PreH3 : (n0 <= 35)) (PreH4 : (problem_46_pre_z n0 )) (PreH5 : (fib4_safe_z n0 )) (PreH6 : (f <> 0)) (PreH7 : (4 <= i)) (PreH8 : (i <= 36)) (PreH9 : (n0 < 4)) (PreH10 : (i = 4)) ,
  (IntArray.seg f 0 (fib4_fill_len_z (n0) (i)) (fib4_prefix_z ((fib4_fill_len_z (n0) (i)))) )
  **  (IntArray.undef_seg f (fib4_fill_len_z (n0) (i)) 100 )
|--
  (IntArray.seg f 0 (fib4_fill_len_z (n0) ((n0 + 1 ))) (fib4_prefix_z ((fib4_fill_len_z (n0) ((n0 + 1 ))))) )
  **  (IntArray.undef_seg f (fib4_fill_len_z (n0) ((n0 + 1 ))) 100 )
.

Definition fib4_entail_wit_10_1 := 
(
forall (n0: Z) (f: Z) (PreH1 : (n0 >= 4)) (PreH2 : (0 <= n0)) (PreH3 : (n0 <= 35)) (PreH4 : (problem_46_pre_z n0 )) (PreH5 : (fib4_safe_z n0 )) (PreH6 : (f <> 0)) ,
  (IntArray.seg f 0 (fib4_fill_len_z (n0) ((n0 + 1 ))) (fib4_prefix_z ((fib4_fill_len_z (n0) ((n0 + 1 ))))) )
  **  (IntArray.undef_seg f (fib4_fill_len_z (n0) ((n0 + 1 ))) 100 )
|--
  “ ((n0 + 1 ) = (fib4_fill_len_z (n0) ((n0 + 1 )))) ” 
  &&  “ (n0 < (n0 + 1 )) ” 
  &&  “ (0 <= n0) ” 
  &&  “ (n0 <= 35) ” 
  &&  “ (problem_46_pre_z n0 ) ” 
  &&  “ (fib4_safe_z n0 ) ” 
  &&  “ (f <> 0) ” 
  &&  “ ((n0 + 1 ) <= 100) ”
  &&  (IntArray.seg f 0 (n0 + 1 ) (fib4_prefix_z ((n0 + 1 ))) )
  **  (IntArray.undef_seg f (n0 + 1 ) 100 )
) \/
(
forall (n0: Z) (f: Z) (PreH1 : (n0 >= 4)) (PreH2 : (0 <= n0)) (PreH3 : (n0 <= 35)) (PreH4 : (problem_46_pre_z n0 )) (PreH5 : (fib4_safe_z n0 )) (PreH6 : (f <> 0)) ,
  (IntArray.seg f 0 (fib4_fill_len_z (n0) ((n0 + 1 ))) (fib4_prefix_z ((fib4_fill_len_z (n0) ((n0 + 1 ))))) )
  **  (IntArray.undef_seg f (fib4_fill_len_z (n0) ((n0 + 1 ))) 100 )
|--
  “ ((n0 + 1 ) = (fib4_fill_len_z (n0) ((n0 + 1 )))) ”
  &&  (IntArray.seg f 0 (n0 + 1 ) (fib4_prefix_z ((n0 + 1 ))) )
  **  (IntArray.undef_seg f (n0 + 1 ) 100 )
).

Definition fib4_entail_wit_10_1_split_goal_1 := 
forall (n0: Z) (f: Z) (PreH1 : (n0 >= 4)) (PreH2 : (0 <= n0)) (PreH3 : (n0 <= 35)) (PreH4 : (problem_46_pre_z n0 )) (PreH5 : (fib4_safe_z n0 )) (PreH6 : (f <> 0)) ,
  (IntArray.seg f 0 (fib4_fill_len_z (n0) ((n0 + 1 ))) (fib4_prefix_z ((fib4_fill_len_z (n0) ((n0 + 1 ))))) )
  **  (IntArray.undef_seg f (fib4_fill_len_z (n0) ((n0 + 1 ))) 100 )
|--
  “ ((n0 + 1 ) = (fib4_fill_len_z (n0) ((n0 + 1 )))) ”
.

Definition fib4_entail_wit_10_1_split_goal_spatial := 
forall (n0: Z) (f: Z) (PreH1 : (n0 >= 4)) (PreH2 : (0 <= n0)) (PreH3 : (n0 <= 35)) (PreH4 : (problem_46_pre_z n0 )) (PreH5 : (fib4_safe_z n0 )) (PreH6 : (f <> 0)) ,
  (IntArray.seg f 0 (fib4_fill_len_z (n0) ((n0 + 1 ))) (fib4_prefix_z ((fib4_fill_len_z (n0) ((n0 + 1 ))))) )
  **  (IntArray.undef_seg f (fib4_fill_len_z (n0) ((n0 + 1 ))) 100 )
|--
  (IntArray.seg f 0 (n0 + 1 ) (fib4_prefix_z ((n0 + 1 ))) )
  **  (IntArray.undef_seg f (n0 + 1 ) 100 )
.

Definition fib4_entail_wit_10_2 := 
(
forall (n0: Z) (f: Z) (PreH1 : (n0 < 4)) (PreH2 : (0 <= n0)) (PreH3 : (n0 <= 35)) (PreH4 : (problem_46_pre_z n0 )) (PreH5 : (fib4_safe_z n0 )) (PreH6 : (f <> 0)) ,
  (IntArray.seg f 0 (fib4_fill_len_z (n0) ((n0 + 1 ))) (fib4_prefix_z ((fib4_fill_len_z (n0) ((n0 + 1 ))))) )
  **  (IntArray.undef_seg f (fib4_fill_len_z (n0) ((n0 + 1 ))) 100 )
|--
  “ (4 = (fib4_fill_len_z (n0) ((n0 + 1 )))) ” 
  &&  “ (n0 < 4) ” 
  &&  “ (0 <= n0) ” 
  &&  “ (n0 <= 35) ” 
  &&  “ (problem_46_pre_z n0 ) ” 
  &&  “ (fib4_safe_z n0 ) ” 
  &&  “ (f <> 0) ” 
  &&  “ (4 <= 100) ”
  &&  (IntArray.seg f 0 4 (fib4_prefix_z (4)) )
  **  (IntArray.undef_seg f 4 100 )
) \/
(
forall (n0: Z) (f: Z) (PreH1 : (n0 < 4)) (PreH2 : (0 <= n0)) (PreH3 : (n0 <= 35)) (PreH4 : (problem_46_pre_z n0 )) (PreH5 : (fib4_safe_z n0 )) (PreH6 : (f <> 0)) ,
  (IntArray.seg f 0 (fib4_fill_len_z (n0) ((n0 + 1 ))) (fib4_prefix_z ((fib4_fill_len_z (n0) ((n0 + 1 ))))) )
  **  (IntArray.undef_seg f (fib4_fill_len_z (n0) ((n0 + 1 ))) 100 )
|--
  “ (4 = (fib4_fill_len_z (n0) ((n0 + 1 )))) ”
  &&  (IntArray.seg f 0 4 (fib4_prefix_z (4)) )
  **  (IntArray.undef_seg f 4 100 )
).

Definition fib4_entail_wit_10_2_split_goal_1 := 
forall (n0: Z) (f: Z) (PreH1 : (n0 < 4)) (PreH2 : (0 <= n0)) (PreH3 : (n0 <= 35)) (PreH4 : (problem_46_pre_z n0 )) (PreH5 : (fib4_safe_z n0 )) (PreH6 : (f <> 0)) ,
  (IntArray.seg f 0 (fib4_fill_len_z (n0) ((n0 + 1 ))) (fib4_prefix_z ((fib4_fill_len_z (n0) ((n0 + 1 ))))) )
  **  (IntArray.undef_seg f (fib4_fill_len_z (n0) ((n0 + 1 ))) 100 )
|--
  “ (4 = (fib4_fill_len_z (n0) ((n0 + 1 )))) ”
.

Definition fib4_entail_wit_10_2_split_goal_spatial := 
forall (n0: Z) (f: Z) (PreH1 : (n0 < 4)) (PreH2 : (0 <= n0)) (PreH3 : (n0 <= 35)) (PreH4 : (problem_46_pre_z n0 )) (PreH5 : (fib4_safe_z n0 )) (PreH6 : (f <> 0)) ,
  (IntArray.seg f 0 (fib4_fill_len_z (n0) ((n0 + 1 ))) (fib4_prefix_z ((fib4_fill_len_z (n0) ((n0 + 1 ))))) )
  **  (IntArray.undef_seg f (fib4_fill_len_z (n0) ((n0 + 1 ))) 100 )
|--
  (IntArray.seg f 0 4 (fib4_prefix_z (4)) )
  **  (IntArray.undef_seg f 4 100 )
.

Definition fib4_entail_wit_11 := 
(
forall (n0: Z) (filled: Z) (f: Z) (PreH1 : (filled = (fib4_fill_len_z (n0) ((n0 + 1 ))))) (PreH2 : (n0 < filled)) (PreH3 : (0 <= n0)) (PreH4 : (n0 <= 35)) (PreH5 : (problem_46_pre_z n0 )) (PreH6 : (fib4_safe_z n0 )) (PreH7 : (f <> 0)) (PreH8 : (filled <= 100)) ,
  (IntArray.seg f 0 filled (fib4_prefix_z (filled)) )
  **  (IntArray.undef_seg f filled 100 )
|--
  “ ((Znth (n0 - 0 ) (fib4_prefix_z (filled)) 0) = (fib4_z (n0))) ” 
  &&  “ (filled = (fib4_fill_len_z (n0) ((n0 + 1 )))) ” 
  &&  “ (n0 < filled) ” 
  &&  “ (0 <= n0) ” 
  &&  “ (n0 <= 35) ” 
  &&  “ (problem_46_pre_z n0 ) ” 
  &&  “ (fib4_safe_z n0 ) ” 
  &&  “ (f <> 0) ” 
  &&  “ (filled <= 100) ”
  &&  (IntArray.seg f 0 filled (fib4_prefix_z (filled)) )
  **  (IntArray.undef_seg f filled 100 )
) \/
(
forall (n0: Z) (filled: Z) (f: Z) (PreH1 : (filled = (fib4_fill_len_z (n0) ((n0 + 1 ))))) (PreH2 : (n0 < filled)) (PreH3 : (0 <= n0)) (PreH4 : (n0 <= 35)) (PreH5 : (problem_46_pre_z n0 )) (PreH6 : (fib4_safe_z n0 )) (PreH7 : (f <> 0)) (PreH8 : (filled <= 100)) ,
  TT && emp 
|--
  “ ((Znth (n0 - 0 ) (fib4_prefix_z (filled)) 0) = (fib4_z (n0))) ”
  &&  emp
).

Definition fib4_entail_wit_11_split_goal_1 := 
forall (n0: Z) (filled: Z) (f: Z) (PreH1 : (filled = (fib4_fill_len_z (n0) ((n0 + 1 ))))) (PreH2 : (n0 < filled)) (PreH3 : (0 <= n0)) (PreH4 : (n0 <= 35)) (PreH5 : (problem_46_pre_z n0 )) (PreH6 : (fib4_safe_z n0 )) (PreH7 : (f <> 0)) (PreH8 : (filled <= 100)) ,
  TT && emp 
|--
  “ ((Znth (n0 - 0 ) (fib4_prefix_z (filled)) 0) = (fib4_z (n0))) ”
.

Definition fib4_return_wit_1 := 
(
forall (n0: Z) (result: Z) (filled: Z) (f: Z) (PreH1 : (result = (fib4_z (n0)))) (PreH2 : (filled = (fib4_fill_len_z (n0) ((n0 + 1 ))))) (PreH3 : (n0 < filled)) (PreH4 : (0 <= n0)) (PreH5 : (n0 <= 35)) (PreH6 : (problem_46_pre_z n0 )) (PreH7 : (fib4_safe_z n0 )) (PreH8 : (f <> 0)) (PreH9 : (filled <= 100)) ,
  TT && emp 
|--
  “ (problem_46_spec_z n0 result ) ”
  &&  emp
) \/
(
forall (n0: Z) (result: Z) (filled: Z) (f: Z) (PreH1 : (result = (fib4_z (n0)))) (PreH2 : (filled = (fib4_fill_len_z (n0) ((n0 + 1 ))))) (PreH3 : (n0 < filled)) (PreH4 : (0 <= n0)) (PreH5 : (n0 <= 35)) (PreH6 : (problem_46_pre_z n0 )) (PreH7 : (fib4_safe_z n0 )) (PreH8 : (f <> 0)) (PreH9 : (filled <= 100)) ,
  TT && emp 
|--
  “ (problem_46_spec_z n0 result ) ”
  &&  emp
).

Definition fib4_return_wit_1_split_goal_1 := 
forall (n0: Z) (result: Z) (filled: Z) (f: Z) (PreH1 : (result = (fib4_z (n0)))) (PreH2 : (filled = (fib4_fill_len_z (n0) ((n0 + 1 ))))) (PreH3 : (n0 < filled)) (PreH4 : (0 <= n0)) (PreH5 : (n0 <= 35)) (PreH6 : (problem_46_pre_z n0 )) (PreH7 : (fib4_safe_z n0 )) (PreH8 : (f <> 0)) (PreH9 : (filled <= 100)) ,
  TT && emp 
|--
  “ (problem_46_spec_z n0 result ) ”
.

Definition fib4_partial_solve_wit_1_pure := 
forall (n_pre: Z) (n0: Z) (PreH1 : (n_pre = n0)) (PreH2 : (0 <= n0)) (PreH3 : (n0 <= 35)) (PreH4 : (problem_46_pre_z n0 )) (PreH5 : (fib4_safe_z n0 )) ,
  ((( &( "f" ) )) # Ptr  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (100 = 100) ”
.

Definition fib4_partial_solve_wit_1_aux := 
forall (n_pre: Z) (n0: Z) (PreH1 : (n_pre = n0)) (PreH2 : (0 <= n0)) (PreH3 : (n0 <= 35)) (PreH4 : (problem_46_pre_z n0 )) (PreH5 : (fib4_safe_z n0 )) ,
  TT && emp 
|--
  “ (100 = 100) ” 
  &&  “ (n_pre = n0) ” 
  &&  “ (0 <= n0) ” 
  &&  “ (n0 <= 35) ” 
  &&  “ (problem_46_pre_z n0 ) ” 
  &&  “ (fib4_safe_z n0 ) ”
  &&  emp
.

Definition fib4_partial_solve_wit_1 := fib4_partial_solve_wit_1_pure -> fib4_partial_solve_wit_1_aux.

Definition fib4_partial_solve_wit_2 := 
forall (n_pre: Z) (n0: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (n_pre = n0)) (PreH3 : (0 <= n0)) (PreH4 : (n0 <= 35)) (PreH5 : (problem_46_pre_z n0 )) (PreH6 : (fib4_safe_z n0 )) ,
  (IntArray.undef_full retval 100 )
|--
  “ (retval <> 0) ” 
  &&  “ (n_pre = n0) ” 
  &&  “ (0 <= n0) ” 
  &&  “ (n0 <= 35) ” 
  &&  “ (problem_46_pre_z n0 ) ” 
  &&  “ (fib4_safe_z n0 ) ”
  &&  (((retval + (0 * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg retval 1 100 )
.

Definition fib4_partial_solve_wit_3 := 
forall (n0: Z) (f: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 35)) (PreH3 : (problem_46_pre_z n0 )) (PreH4 : (fib4_safe_z n0 )) (PreH5 : (f <> 0)) ,
  (IntArray.seg f 0 1 (cons (0) ((@nil Z))) )
  **  (IntArray.undef_seg f 1 100 )
|--
  “ (0 <= n0) ” 
  &&  “ (n0 <= 35) ” 
  &&  “ (problem_46_pre_z n0 ) ” 
  &&  “ (fib4_safe_z n0 ) ” 
  &&  “ (f <> 0) ”
  &&  (((f + (1 * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg f (1 + 1 ) 100 )
  **  (IntArray.seg f 0 1 (cons (0) ((@nil Z))) )
.

Definition fib4_partial_solve_wit_4 := 
forall (n0: Z) (f: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 35)) (PreH3 : (problem_46_pre_z n0 )) (PreH4 : (fib4_safe_z n0 )) (PreH5 : (f <> 0)) ,
  (IntArray.seg f 0 2 (cons (0) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg f 2 100 )
|--
  “ (0 <= n0) ” 
  &&  “ (n0 <= 35) ” 
  &&  “ (problem_46_pre_z n0 ) ” 
  &&  “ (fib4_safe_z n0 ) ” 
  &&  “ (f <> 0) ”
  &&  (((f + (2 * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg f (2 + 1 ) 100 )
  **  (IntArray.seg f 0 2 (cons (0) ((cons (0) ((@nil Z))))) )
.

Definition fib4_partial_solve_wit_5 := 
forall (n0: Z) (f: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 35)) (PreH3 : (problem_46_pre_z n0 )) (PreH4 : (fib4_safe_z n0 )) (PreH5 : (f <> 0)) ,
  (IntArray.seg f 0 3 (cons (0) ((cons (0) ((cons (2) ((@nil Z))))))) )
  **  (IntArray.undef_seg f 3 100 )
|--
  “ (0 <= n0) ” 
  &&  “ (n0 <= 35) ” 
  &&  “ (problem_46_pre_z n0 ) ” 
  &&  “ (fib4_safe_z n0 ) ” 
  &&  “ (f <> 0) ”
  &&  (((f + (3 * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg f (3 + 1 ) 100 )
  **  (IntArray.seg f 0 3 (cons (0) ((cons (0) ((cons (2) ((@nil Z))))))) )
.

Definition fib4_partial_solve_wit_6 := 
forall (n0: Z) (f: Z) (i: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 35)) (PreH3 : (problem_46_pre_z n0 )) (PreH4 : (fib4_safe_z n0 )) (PreH5 : (f <> 0)) (PreH6 : (4 <= i)) (PreH7 : (i <= n0)) (PreH8 : ((fib4_fill_len_z (n0) (i)) = i)) ,
  (IntArray.seg f 0 i (fib4_prefix_z (i)) )
  **  (IntArray.undef_seg f i 100 )
|--
  “ (0 <= n0) ” 
  &&  “ (n0 <= 35) ” 
  &&  “ (problem_46_pre_z n0 ) ” 
  &&  “ (fib4_safe_z n0 ) ” 
  &&  “ (f <> 0) ” 
  &&  “ (4 <= i) ” 
  &&  “ (i <= n0) ” 
  &&  “ ((fib4_fill_len_z (n0) (i)) = i) ”
  &&  (((f + ((i - 1 ) * sizeof(INT) ) )) # Int  |-> (Znth ((i - 1 ) - 0 ) (fib4_prefix_z (i)) 0))
  **  (IntArray.missing_i f (i - 1 ) 0 i (fib4_prefix_z (i)) )
  **  (IntArray.undef_seg f i 100 )
.

Definition fib4_partial_solve_wit_7 := 
forall (n0: Z) (f: Z) (i: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 35)) (PreH3 : (problem_46_pre_z n0 )) (PreH4 : (fib4_safe_z n0 )) (PreH5 : (f <> 0)) (PreH6 : (4 <= i)) (PreH7 : (i <= n0)) (PreH8 : ((fib4_fill_len_z (n0) (i)) = i)) ,
  (IntArray.seg f 0 i (fib4_prefix_z (i)) )
  **  (IntArray.undef_seg f i 100 )
|--
  “ (0 <= n0) ” 
  &&  “ (n0 <= 35) ” 
  &&  “ (problem_46_pre_z n0 ) ” 
  &&  “ (fib4_safe_z n0 ) ” 
  &&  “ (f <> 0) ” 
  &&  “ (4 <= i) ” 
  &&  “ (i <= n0) ” 
  &&  “ ((fib4_fill_len_z (n0) (i)) = i) ”
  &&  (((f + ((i - 2 ) * sizeof(INT) ) )) # Int  |-> (Znth ((i - 2 ) - 0 ) (fib4_prefix_z (i)) 0))
  **  (IntArray.missing_i f (i - 2 ) 0 i (fib4_prefix_z (i)) )
  **  (IntArray.undef_seg f i 100 )
.

Definition fib4_partial_solve_wit_8 := 
forall (n0: Z) (f: Z) (i: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 35)) (PreH3 : (problem_46_pre_z n0 )) (PreH4 : (fib4_safe_z n0 )) (PreH5 : (f <> 0)) (PreH6 : (4 <= i)) (PreH7 : (i <= n0)) (PreH8 : ((fib4_fill_len_z (n0) (i)) = i)) ,
  (IntArray.seg f 0 i (fib4_prefix_z (i)) )
  **  (IntArray.undef_seg f i 100 )
|--
  “ (0 <= n0) ” 
  &&  “ (n0 <= 35) ” 
  &&  “ (problem_46_pre_z n0 ) ” 
  &&  “ (fib4_safe_z n0 ) ” 
  &&  “ (f <> 0) ” 
  &&  “ (4 <= i) ” 
  &&  “ (i <= n0) ” 
  &&  “ ((fib4_fill_len_z (n0) (i)) = i) ”
  &&  (((f + ((i - 3 ) * sizeof(INT) ) )) # Int  |-> (Znth ((i - 3 ) - 0 ) (fib4_prefix_z (i)) 0))
  **  (IntArray.missing_i f (i - 3 ) 0 i (fib4_prefix_z (i)) )
  **  (IntArray.undef_seg f i 100 )
.

Definition fib4_partial_solve_wit_9 := 
forall (n0: Z) (f: Z) (i: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 35)) (PreH3 : (problem_46_pre_z n0 )) (PreH4 : (fib4_safe_z n0 )) (PreH5 : (f <> 0)) (PreH6 : (4 <= i)) (PreH7 : (i <= n0)) (PreH8 : ((fib4_fill_len_z (n0) (i)) = i)) ,
  (IntArray.seg f 0 i (fib4_prefix_z (i)) )
  **  (IntArray.undef_seg f i 100 )
|--
  “ (0 <= n0) ” 
  &&  “ (n0 <= 35) ” 
  &&  “ (problem_46_pre_z n0 ) ” 
  &&  “ (fib4_safe_z n0 ) ” 
  &&  “ (f <> 0) ” 
  &&  “ (4 <= i) ” 
  &&  “ (i <= n0) ” 
  &&  “ ((fib4_fill_len_z (n0) (i)) = i) ”
  &&  (((f + ((i - 4 ) * sizeof(INT) ) )) # Int  |-> (Znth ((i - 4 ) - 0 ) (fib4_prefix_z (i)) 0))
  **  (IntArray.missing_i f (i - 4 ) 0 i (fib4_prefix_z (i)) )
  **  (IntArray.undef_seg f i 100 )
.

Definition fib4_partial_solve_wit_10 := 
forall (n0: Z) (f: Z) (i: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 35)) (PreH3 : (problem_46_pre_z n0 )) (PreH4 : (fib4_safe_z n0 )) (PreH5 : (f <> 0)) (PreH6 : (4 <= i)) (PreH7 : (i <= n0)) (PreH8 : ((fib4_fill_len_z (n0) (i)) = i)) ,
  (IntArray.seg f 0 i (fib4_prefix_z (i)) )
  **  (IntArray.undef_seg f i 100 )
|--
  “ (0 <= n0) ” 
  &&  “ (n0 <= 35) ” 
  &&  “ (problem_46_pre_z n0 ) ” 
  &&  “ (fib4_safe_z n0 ) ” 
  &&  “ (f <> 0) ” 
  &&  “ (4 <= i) ” 
  &&  “ (i <= n0) ” 
  &&  “ ((fib4_fill_len_z (n0) (i)) = i) ”
  &&  (((f + (i * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg f (i + 1 ) 100 )
  **  (IntArray.seg f 0 i (fib4_prefix_z (i)) )
.

Definition fib4_partial_solve_wit_11 := 
forall (n0: Z) (filled: Z) (f: Z) (PreH1 : (filled = (fib4_fill_len_z (n0) ((n0 + 1 ))))) (PreH2 : (n0 < filled)) (PreH3 : (0 <= n0)) (PreH4 : (n0 <= 35)) (PreH5 : (problem_46_pre_z n0 )) (PreH6 : (fib4_safe_z n0 )) (PreH7 : (f <> 0)) (PreH8 : (filled <= 100)) ,
  (IntArray.seg f 0 filled (fib4_prefix_z (filled)) )
  **  (IntArray.undef_seg f filled 100 )
|--
  “ (filled = (fib4_fill_len_z (n0) ((n0 + 1 )))) ” 
  &&  “ (n0 < filled) ” 
  &&  “ (0 <= n0) ” 
  &&  “ (n0 <= 35) ” 
  &&  “ (problem_46_pre_z n0 ) ” 
  &&  “ (fib4_safe_z n0 ) ” 
  &&  “ (f <> 0) ” 
  &&  “ (filled <= 100) ”
  &&  (((f + (n0 * sizeof(INT) ) )) # Int  |-> (Znth (n0 - 0 ) (fib4_prefix_z (filled)) 0))
  **  (IntArray.missing_i f n0 0 filled (fib4_prefix_z (filled)) )
  **  (IntArray.undef_seg f filled 100 )
.

Definition fib4_partial_solve_wit_12_pure := 
forall (n0: Z) (result: Z) (filled: Z) (f: Z) (PreH1 : (result = (fib4_z (n0)))) (PreH2 : (filled = (fib4_fill_len_z (n0) ((n0 + 1 ))))) (PreH3 : (n0 < filled)) (PreH4 : (0 <= n0)) (PreH5 : (n0 <= 35)) (PreH6 : (problem_46_pre_z n0 )) (PreH7 : (fib4_safe_z n0 )) (PreH8 : (f <> 0)) (PreH9 : (filled <= 100)) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "result" ) )) # Int  |-> result)
  **  ((( &( "filled" ) )) # Int  |-> filled)
  **  ((( &( "f" ) )) # Ptr  |-> f)
  **  (IntArray.seg f 0 filled (fib4_prefix_z (filled)) )
  **  (IntArray.undef_seg f filled 100 )
|--
  “ (f <> 0) ” 
  &&  “ (0 <= filled) ” 
  &&  “ (filled <= 100) ” 
  &&  “ (100 = 100) ”
.

Definition fib4_partial_solve_wit_12_aux := 
forall (n0: Z) (result: Z) (filled: Z) (f: Z) (PreH1 : (result = (fib4_z (n0)))) (PreH2 : (filled = (fib4_fill_len_z (n0) ((n0 + 1 ))))) (PreH3 : (n0 < filled)) (PreH4 : (0 <= n0)) (PreH5 : (n0 <= 35)) (PreH6 : (problem_46_pre_z n0 )) (PreH7 : (fib4_safe_z n0 )) (PreH8 : (f <> 0)) (PreH9 : (filled <= 100)) ,
  (IntArray.seg f 0 filled (fib4_prefix_z (filled)) )
  **  (IntArray.undef_seg f filled 100 )
|--
  “ (f <> 0) ” 
  &&  “ (0 <= filled) ” 
  &&  “ (filled <= 100) ” 
  &&  “ (100 = 100) ” 
  &&  “ (result = (fib4_z (n0))) ” 
  &&  “ (filled = (fib4_fill_len_z (n0) ((n0 + 1 )))) ” 
  &&  “ (n0 < filled) ” 
  &&  “ (0 <= n0) ” 
  &&  “ (n0 <= 35) ” 
  &&  “ (problem_46_pre_z n0 ) ” 
  &&  “ (fib4_safe_z n0 ) ” 
  &&  “ (f <> 0) ” 
  &&  “ (filled <= 100) ”
  &&  (IntArray.seg f 0 filled (fib4_prefix_z (filled)) )
  **  (IntArray.undef_seg f filled 100 )
.

Definition fib4_partial_solve_wit_12 := fib4_partial_solve_wit_12_pure -> fib4_partial_solve_wit_12_aux.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_fib4_safety_wit_1 : fib4_safety_wit_1.
Axiom proof_of_fib4_safety_wit_2 : fib4_safety_wit_2.
Axiom proof_of_fib4_safety_wit_3 : fib4_safety_wit_3.
Axiom proof_of_fib4_safety_wit_4 : fib4_safety_wit_4.
Axiom proof_of_fib4_safety_wit_5 : fib4_safety_wit_5.
Axiom proof_of_fib4_safety_wit_6 : fib4_safety_wit_6.
Axiom proof_of_fib4_safety_wit_7 : fib4_safety_wit_7.
Axiom proof_of_fib4_safety_wit_8 : fib4_safety_wit_8.
Axiom proof_of_fib4_safety_wit_9 : fib4_safety_wit_9.
Axiom proof_of_fib4_safety_wit_10 : fib4_safety_wit_10.
Axiom proof_of_fib4_safety_wit_11 : fib4_safety_wit_11.
Axiom proof_of_fib4_safety_wit_12 : fib4_safety_wit_12.
Axiom proof_of_fib4_safety_wit_13 : fib4_safety_wit_13.
Axiom proof_of_fib4_safety_wit_14 : fib4_safety_wit_14.
Axiom proof_of_fib4_safety_wit_15 : fib4_safety_wit_15.
Axiom proof_of_fib4_safety_wit_16 : fib4_safety_wit_16.
Axiom proof_of_fib4_safety_wit_17 : fib4_safety_wit_17.
Axiom proof_of_fib4_safety_wit_18 : fib4_safety_wit_18.
Axiom proof_of_fib4_safety_wit_19 : fib4_safety_wit_19.
Axiom proof_of_fib4_safety_wit_20 : fib4_safety_wit_20.
Axiom proof_of_fib4_safety_wit_21 : fib4_safety_wit_21.
Axiom proof_of_fib4_safety_wit_22 : fib4_safety_wit_22.
Axiom proof_of_fib4_safety_wit_23 : fib4_safety_wit_23.
Axiom proof_of_fib4_safety_wit_24 : fib4_safety_wit_24.
Axiom proof_of_fib4_safety_wit_25 : fib4_safety_wit_25.
Axiom proof_of_fib4_safety_wit_26 : fib4_safety_wit_26.
Axiom proof_of_fib4_safety_wit_27 : fib4_safety_wit_27.
Axiom proof_of_fib4_safety_wit_28 : fib4_safety_wit_28.
Axiom proof_of_fib4_entail_wit_1 : fib4_entail_wit_1.
Axiom proof_of_fib4_entail_wit_2 : fib4_entail_wit_2.
Axiom proof_of_fib4_entail_wit_3 : fib4_entail_wit_3.
Axiom proof_of_fib4_entail_wit_4 : fib4_entail_wit_4.
Axiom proof_of_fib4_entail_wit_5 : fib4_entail_wit_5.
Axiom proof_of_fib4_entail_wit_6 : fib4_entail_wit_6.
Axiom proof_of_fib4_entail_wit_7 : fib4_entail_wit_7.
Axiom proof_of_fib4_entail_wit_8 : fib4_entail_wit_8.
Axiom proof_of_fib4_entail_wit_9_1 : fib4_entail_wit_9_1.
Axiom proof_of_fib4_entail_wit_9_2 : fib4_entail_wit_9_2.
Axiom proof_of_fib4_entail_wit_10_1 : fib4_entail_wit_10_1.
Axiom proof_of_fib4_entail_wit_10_2 : fib4_entail_wit_10_2.
Axiom proof_of_fib4_entail_wit_11 : fib4_entail_wit_11.
Axiom proof_of_fib4_return_wit_1 : fib4_return_wit_1.
Axiom proof_of_fib4_partial_solve_wit_1_pure : fib4_partial_solve_wit_1_pure.
Axiom proof_of_fib4_partial_solve_wit_1 : fib4_partial_solve_wit_1.
Axiom proof_of_fib4_partial_solve_wit_2 : fib4_partial_solve_wit_2.
Axiom proof_of_fib4_partial_solve_wit_3 : fib4_partial_solve_wit_3.
Axiom proof_of_fib4_partial_solve_wit_4 : fib4_partial_solve_wit_4.
Axiom proof_of_fib4_partial_solve_wit_5 : fib4_partial_solve_wit_5.
Axiom proof_of_fib4_partial_solve_wit_6 : fib4_partial_solve_wit_6.
Axiom proof_of_fib4_partial_solve_wit_7 : fib4_partial_solve_wit_7.
Axiom proof_of_fib4_partial_solve_wit_8 : fib4_partial_solve_wit_8.
Axiom proof_of_fib4_partial_solve_wit_9 : fib4_partial_solve_wit_9.
Axiom proof_of_fib4_partial_solve_wit_10 : fib4_partial_solve_wit_10.
Axiom proof_of_fib4_partial_solve_wit_11 : fib4_partial_solve_wit_11.
Axiom proof_of_fib4_partial_solve_wit_12_pure : fib4_partial_solve_wit_12_pure.
Axiom proof_of_fib4_partial_solve_wit_12 : fib4_partial_solve_wit_12.

End VC_Correct.
