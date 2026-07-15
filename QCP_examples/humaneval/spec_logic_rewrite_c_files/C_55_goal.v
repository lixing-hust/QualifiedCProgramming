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
Require Import coins_55.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_proof.

(*----- Function fib -----*)

Definition fib_safety_wit_1 := 
forall (n_pre: Z) (n0: Z) (PreH1 : (n_pre = n0)) (PreH2 : (0 <= n0)) (PreH3 : (n0 <= 46)) (PreH4 : (problem_55_pre_z n0 )) (PreH5 : (fib_safe_z n0 )) ,
  ((( &( "f" ) )) # Ptr  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (1000 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1000) ”
.

Definition fib_safety_wit_2 := 
forall (n_pre: Z) (n0: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (n_pre = n0)) (PreH3 : (0 <= n0)) (PreH4 : (n0 <= 46)) (PreH5 : (problem_55_pre_z n0 )) (PreH6 : (fib_safe_z n0 )) ,
  (IntArray.undef_full retval 1000 )
  **  ((( &( "f" ) )) # Ptr  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition fib_safety_wit_3 := 
forall (n_pre: Z) (n0: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (n_pre = n0)) (PreH3 : (0 <= n0)) (PreH4 : (n0 <= 46)) (PreH5 : (problem_55_pre_z n0 )) (PreH6 : (fib_safe_z n0 )) ,
  (IntArray.undef_full retval 1000 )
  **  ((( &( "f" ) )) # Ptr  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition fib_safety_wit_4 := 
forall (n_pre: Z) (n0: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (n_pre = n0)) (PreH3 : (0 <= n0)) (PreH4 : (n0 <= 46)) (PreH5 : (problem_55_pre_z n0 )) (PreH6 : (fib_safe_z n0 )) ,
  (((retval + (0 * sizeof(INT) ) )) # Int  |-> 0)
  **  (IntArray.undef_seg retval 1 1000 )
  **  ((( &( "f" ) )) # Ptr  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition fib_safety_wit_5 := 
forall (n_pre: Z) (n0: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (n_pre = n0)) (PreH3 : (0 <= n0)) (PreH4 : (n0 <= 46)) (PreH5 : (problem_55_pre_z n0 )) (PreH6 : (fib_safe_z n0 )) ,
  (((retval + (0 * sizeof(INT) ) )) # Int  |-> 0)
  **  (IntArray.undef_seg retval 1 1000 )
  **  ((( &( "f" ) )) # Ptr  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition fib_safety_wit_6 := 
forall (n0: Z) (f: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 46)) (PreH3 : (problem_55_pre_z n0 )) (PreH4 : (fib_safe_z n0 )) (PreH5 : (f <> 0)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "f" ) )) # Ptr  |-> f)
  **  (IntArray.seg f 0 2 (fib_prefix_z (2)) )
  **  (IntArray.undef_seg f 2 1000 )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition fib_safety_wit_7 := 
forall (n0: Z) (i: Z) (f: Z) (PreH1 : (i <= n0)) (PreH2 : (0 <= n0)) (PreH3 : (n0 <= 46)) (PreH4 : (problem_55_pre_z n0 )) (PreH5 : (fib_safe_z n0 )) (PreH6 : (f <> 0)) (PreH7 : (2 <= i)) (PreH8 : (i <= 47)) (PreH9 : (n0 < 2)) (PreH10 : (i = 2)) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "f" ) )) # Ptr  |-> f)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.seg f 0 (fib_fill_len_z (n0) (i)) (fib_prefix_z ((fib_fill_len_z (n0) (i)))) )
  **  (IntArray.undef_seg f (fib_fill_len_z (n0) (i)) 1000 )
|--
  “ False ”
.

Definition fib_safety_wit_8 := 
forall (n0: Z) (f: Z) (i: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 46)) (PreH3 : (problem_55_pre_z n0 )) (PreH4 : (fib_safe_z n0 )) (PreH5 : (f <> 0)) (PreH6 : (2 <= i)) (PreH7 : (i <= n0)) (PreH8 : ((fib_fill_len_z (n0) (i)) = i)) ,
  ((( &( "a" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "f" ) )) # Ptr  |-> f)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.seg f 0 i (fib_prefix_z (i)) )
  **  (IntArray.undef_seg f i 1000 )
|--
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition fib_safety_wit_9 := 
forall (n0: Z) (f: Z) (i: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 46)) (PreH3 : (problem_55_pre_z n0 )) (PreH4 : (fib_safe_z n0 )) (PreH5 : (f <> 0)) (PreH6 : (2 <= i)) (PreH7 : (i <= n0)) (PreH8 : ((fib_fill_len_z (n0) (i)) = i)) ,
  ((( &( "a" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "f" ) )) # Ptr  |-> f)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.seg f 0 i (fib_prefix_z (i)) )
  **  (IntArray.undef_seg f i 1000 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition fib_safety_wit_10 := 
forall (n0: Z) (f: Z) (i: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 46)) (PreH3 : (problem_55_pre_z n0 )) (PreH4 : (fib_safe_z n0 )) (PreH5 : (f <> 0)) (PreH6 : (2 <= i)) (PreH7 : (i <= n0)) (PreH8 : ((fib_fill_len_z (n0) (i)) = i)) ,
  ((( &( "b" ) )) # Int  |->_)
  **  (IntArray.seg f 0 i (fib_prefix_z (i)) )
  **  ((( &( "a" ) )) # Int  |-> (Znth ((i - 1 ) - 0 ) (fib_prefix_z (i)) 0))
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "f" ) )) # Ptr  |-> f)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_seg f i 1000 )
|--
  “ ((i - 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 2 )) ”
.

Definition fib_safety_wit_11 := 
forall (n0: Z) (f: Z) (i: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 46)) (PreH3 : (problem_55_pre_z n0 )) (PreH4 : (fib_safe_z n0 )) (PreH5 : (f <> 0)) (PreH6 : (2 <= i)) (PreH7 : (i <= n0)) (PreH8 : ((fib_fill_len_z (n0) (i)) = i)) ,
  ((( &( "b" ) )) # Int  |->_)
  **  (IntArray.seg f 0 i (fib_prefix_z (i)) )
  **  ((( &( "a" ) )) # Int  |-> (Znth ((i - 1 ) - 0 ) (fib_prefix_z (i)) 0))
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "f" ) )) # Ptr  |-> f)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_seg f i 1000 )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition fib_safety_wit_12 := 
(
forall (n0: Z) (f: Z) (i: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 46)) (PreH3 : (problem_55_pre_z n0 )) (PreH4 : (fib_safe_z n0 )) (PreH5 : (f <> 0)) (PreH6 : (2 <= i)) (PreH7 : (i <= n0)) (PreH8 : ((fib_fill_len_z (n0) (i)) = i)) ,
  (IntArray.seg f 0 i (fib_prefix_z (i)) )
  **  ((( &( "b" ) )) # Int  |-> (Znth ((i - 2 ) - 0 ) (fib_prefix_z (i)) 0))
  **  ((( &( "a" ) )) # Int  |-> (Znth ((i - 1 ) - 0 ) (fib_prefix_z (i)) 0))
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "f" ) )) # Ptr  |-> f)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_seg f i 1000 )
|--
  “ (((Znth ((i - 1 ) - 0 ) (fib_prefix_z (i)) 0) + (Znth ((i - 2 ) - 0 ) (fib_prefix_z (i)) 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth ((i - 1 ) - 0 ) (fib_prefix_z (i)) 0) + (Znth ((i - 2 ) - 0 ) (fib_prefix_z (i)) 0) )) ”
) \/
(
forall (n0: Z) (f: Z) (i: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 46)) (PreH3 : (problem_55_pre_z n0 )) (PreH4 : (fib_safe_z n0 )) (PreH5 : (f <> 0)) (PreH6 : (2 <= i)) (PreH7 : (i <= n0)) (PreH8 : ((fib_fill_len_z (n0) (i)) = i)) ,
  (IntArray.seg f 0 i (fib_prefix_z (i)) )
  **  ((( &( "b" ) )) # Int  |-> (Znth ((i - 2 ) - 0 ) (fib_prefix_z (i)) 0))
  **  ((( &( "a" ) )) # Int  |-> (Znth ((i - 1 ) - 0 ) (fib_prefix_z (i)) 0))
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "f" ) )) # Ptr  |-> f)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_seg f i 1000 )
|--
  “ (((Znth ((i - 1 ) - 0 ) (fib_prefix_z (i)) 0) + (Znth ((i - 2 ) - 0 ) (fib_prefix_z (i)) 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth ((i - 1 ) - 0 ) (fib_prefix_z (i)) 0) + (Znth ((i - 2 ) - 0 ) (fib_prefix_z (i)) 0) )) ”
).

Definition fib_safety_wit_12_split_goal_1 := 
forall (n0: Z) (f: Z) (i: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 46)) (PreH3 : (problem_55_pre_z n0 )) (PreH4 : (fib_safe_z n0 )) (PreH5 : (f <> 0)) (PreH6 : (2 <= i)) (PreH7 : (i <= n0)) (PreH8 : ((fib_fill_len_z (n0) (i)) = i)) ,
  (IntArray.seg f 0 i (fib_prefix_z (i)) )
  **  ((( &( "b" ) )) # Int  |-> (Znth ((i - 2 ) - 0 ) (fib_prefix_z (i)) 0))
  **  ((( &( "a" ) )) # Int  |-> (Znth ((i - 1 ) - 0 ) (fib_prefix_z (i)) 0))
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "f" ) )) # Ptr  |-> f)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_seg f i 1000 )
|--
  “ (((Znth ((i - 1 ) - 0 ) (fib_prefix_z (i)) 0) + (Znth ((i - 2 ) - 0 ) (fib_prefix_z (i)) 0) ) <= INT_MAX) ”
.

Definition fib_safety_wit_12_split_goal_2 := 
forall (n0: Z) (f: Z) (i: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 46)) (PreH3 : (problem_55_pre_z n0 )) (PreH4 : (fib_safe_z n0 )) (PreH5 : (f <> 0)) (PreH6 : (2 <= i)) (PreH7 : (i <= n0)) (PreH8 : ((fib_fill_len_z (n0) (i)) = i)) ,
  (IntArray.seg f 0 i (fib_prefix_z (i)) )
  **  ((( &( "b" ) )) # Int  |-> (Znth ((i - 2 ) - 0 ) (fib_prefix_z (i)) 0))
  **  ((( &( "a" ) )) # Int  |-> (Znth ((i - 1 ) - 0 ) (fib_prefix_z (i)) 0))
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "f" ) )) # Ptr  |-> f)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_seg f i 1000 )
|--
  “ ((INT_MIN) <= ((Znth ((i - 1 ) - 0 ) (fib_prefix_z (i)) 0) + (Znth ((i - 2 ) - 0 ) (fib_prefix_z (i)) 0) )) ”
.

Definition fib_safety_wit_13 := 
forall (n0: Z) (f: Z) (i: Z) (a: Z) (b: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 46)) (PreH3 : (problem_55_pre_z n0 )) (PreH4 : (fib_safe_z n0 )) (PreH5 : (f <> 0)) (PreH6 : (2 <= i)) (PreH7 : (i <= n0)) (PreH8 : (a = (fib_z ((i - 1 ))))) (PreH9 : (b = (fib_z ((i - 2 ))))) (PreH10 : ((fib_z (i)) = (a + b ))) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "f" ) )) # Ptr  |-> f)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.seg f 0 (i + 1 ) (fib_prefix_z ((i + 1 ))) )
  **  (IntArray.undef_seg f (i + 1 ) 1000 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition fib_safety_wit_14 := 
forall (n0: Z) (f: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 46)) (PreH3 : (problem_55_pre_z n0 )) (PreH4 : (fib_safe_z n0 )) (PreH5 : (f <> 0)) ,
  ((( &( "filled" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "f" ) )) # Ptr  |-> f)
  **  (IntArray.seg f 0 (fib_fill_len_z (n0) ((n0 + 1 ))) (fib_prefix_z ((fib_fill_len_z (n0) ((n0 + 1 ))))) )
  **  (IntArray.undef_seg f (fib_fill_len_z (n0) ((n0 + 1 ))) 1000 )
|--
  “ ((n0 + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n0 + 1 )) ”
.

Definition fib_safety_wit_15 := 
forall (n0: Z) (f: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 46)) (PreH3 : (problem_55_pre_z n0 )) (PreH4 : (fib_safe_z n0 )) (PreH5 : (f <> 0)) ,
  ((( &( "filled" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "f" ) )) # Ptr  |-> f)
  **  (IntArray.seg f 0 (fib_fill_len_z (n0) ((n0 + 1 ))) (fib_prefix_z ((fib_fill_len_z (n0) ((n0 + 1 ))))) )
  **  (IntArray.undef_seg f (fib_fill_len_z (n0) ((n0 + 1 ))) 1000 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition fib_safety_wit_16 := 
forall (n0: Z) (f: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 46)) (PreH3 : (problem_55_pre_z n0 )) (PreH4 : (fib_safe_z n0 )) (PreH5 : (f <> 0)) ,
  ((( &( "filled" ) )) # Int  |-> (n0 + 1 ))
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "f" ) )) # Ptr  |-> f)
  **  (IntArray.seg f 0 (fib_fill_len_z (n0) ((n0 + 1 ))) (fib_prefix_z ((fib_fill_len_z (n0) ((n0 + 1 ))))) )
  **  (IntArray.undef_seg f (fib_fill_len_z (n0) ((n0 + 1 ))) 1000 )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition fib_safety_wit_17 := 
forall (n0: Z) (f: Z) (PreH1 : (n0 < 2)) (PreH2 : (0 <= n0)) (PreH3 : (n0 <= 46)) (PreH4 : (problem_55_pre_z n0 )) (PreH5 : (fib_safe_z n0 )) (PreH6 : (f <> 0)) ,
  ((( &( "filled" ) )) # Int  |-> (n0 + 1 ))
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "f" ) )) # Ptr  |-> f)
  **  (IntArray.seg f 0 (fib_fill_len_z (n0) ((n0 + 1 ))) (fib_prefix_z ((fib_fill_len_z (n0) ((n0 + 1 ))))) )
  **  (IntArray.undef_seg f (fib_fill_len_z (n0) ((n0 + 1 ))) 1000 )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition fib_safety_wit_18 := 
forall (n0: Z) (result: Z) (filled: Z) (f: Z) (PreH1 : (result = (fib_z (n0)))) (PreH2 : (filled = (fib_fill_len_z (n0) ((n0 + 1 ))))) (PreH3 : (n0 < filled)) (PreH4 : (0 <= n0)) (PreH5 : (n0 <= 46)) (PreH6 : (problem_55_pre_z n0 )) (PreH7 : (fib_safe_z n0 )) (PreH8 : (f <> 0)) (PreH9 : (filled <= 1000)) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "result" ) )) # Int  |-> result)
  **  ((( &( "filled" ) )) # Int  |-> filled)
  **  ((( &( "f" ) )) # Ptr  |-> f)
  **  (IntArray.seg f 0 filled (fib_prefix_z (filled)) )
  **  (IntArray.undef_seg f filled 1000 )
|--
  “ (1000 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1000) ”
.

Definition fib_entail_wit_1 := 
(
forall (n_pre: Z) (n0: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (n_pre = n0)) (PreH3 : (0 <= n0)) (PreH4 : (n0 <= 46)) (PreH5 : (problem_55_pre_z n0 )) (PreH6 : (fib_safe_z n0 )) ,
  (((retval + (1 * sizeof(INT) ) )) # Int  |-> 1)
  **  (IntArray.undef_seg retval (1 + 1 ) 1000 )
  **  (((retval + (0 * sizeof(INT) ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (0 <= n0) ” 
  &&  “ (n0 <= 46) ” 
  &&  “ (problem_55_pre_z n0 ) ” 
  &&  “ (fib_safe_z n0 ) ” 
  &&  “ (retval <> 0) ”
  &&  ((( &( "n" ) )) # Int  |-> n0)
  **  (IntArray.seg retval 0 2 (fib_prefix_z (2)) )
  **  (IntArray.undef_seg retval 2 1000 )
) \/
(
forall (n_pre: Z) (n0: Z) (retval: Z) (PreH1 : (0 <= INT_MAX)) (PreH2 : (1 <= INT_MAX)) (PreH3 : (0 >= INT_MIN)) (PreH4 : (1 >= INT_MIN)) (PreH5 : (retval <> 0)) (PreH6 : (n_pre = n0)) (PreH7 : (0 <= n0)) (PreH8 : (n0 <= 46)) (PreH9 : (problem_55_pre_z n0 )) (PreH10 : (fib_safe_z n0 )) ,
  (((retval + (1 * sizeof(INT) ) )) # Int  |-> 1)
  **  (((retval + (0 * sizeof(INT) ) )) # Int  |-> 0)
|--
  (IntArray.seg retval 0 2 (fib_prefix_z (2)) )
).

Definition fib_entail_wit_1_split_goal_spatial := 
forall (n_pre: Z) (n0: Z) (retval: Z) (PreH1 : (0 <= INT_MAX)) (PreH2 : (1 <= INT_MAX)) (PreH3 : (0 >= INT_MIN)) (PreH4 : (1 >= INT_MIN)) (PreH5 : (retval <> 0)) (PreH6 : (n_pre = n0)) (PreH7 : (0 <= n0)) (PreH8 : (n0 <= 46)) (PreH9 : (problem_55_pre_z n0 )) (PreH10 : (fib_safe_z n0 )) ,
  (((retval + (1 * sizeof(INT) ) )) # Int  |-> 1)
  **  (((retval + (0 * sizeof(INT) ) )) # Int  |-> 0)
|--
  (IntArray.seg retval 0 2 (fib_prefix_z (2)) )
.

Definition fib_entail_wit_2 := 
forall (n0: Z) (f: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 46)) (PreH3 : (problem_55_pre_z n0 )) (PreH4 : (fib_safe_z n0 )) (PreH5 : (f <> 0)) ,
  (IntArray.seg f 0 2 (fib_prefix_z (2)) )
  **  (IntArray.undef_seg f 2 1000 )
|--
  (“ (0 <= n0) ” 
  &&  “ (n0 <= 46) ” 
  &&  “ (problem_55_pre_z n0 ) ” 
  &&  “ (fib_safe_z n0 ) ” 
  &&  “ (f <> 0) ” 
  &&  “ (2 <= 2) ” 
  &&  “ (2 <= 47) ” 
  &&  “ (n0 < 2) ” 
  &&  “ (2 = 2) ”
  &&  (IntArray.seg f 0 (fib_fill_len_z (n0) (2)) (fib_prefix_z ((fib_fill_len_z (n0) (2)))) )
  **  (IntArray.undef_seg f (fib_fill_len_z (n0) (2)) 1000 ))
  ||
  (“ (0 <= n0) ” 
  &&  “ (n0 <= 46) ” 
  &&  “ (problem_55_pre_z n0 ) ” 
  &&  “ (fib_safe_z n0 ) ” 
  &&  “ (f <> 0) ” 
  &&  “ (2 <= 2) ” 
  &&  “ (2 <= 47) ” 
  &&  “ (2 <= n0) ” 
  &&  “ (2 <= (n0 + 1 )) ”
  &&  (IntArray.seg f 0 (fib_fill_len_z (n0) (2)) (fib_prefix_z ((fib_fill_len_z (n0) (2)))) )
  **  (IntArray.undef_seg f (fib_fill_len_z (n0) (2)) 1000 ))
.

Definition fib_entail_wit_3 := 
(
forall (n0: Z) (i: Z) (f: Z) (PreH1 : (i <= n0)) (PreH2 : (0 <= n0)) (PreH3 : (n0 <= 46)) (PreH4 : (problem_55_pre_z n0 )) (PreH5 : (fib_safe_z n0 )) (PreH6 : (f <> 0)) (PreH7 : (2 <= i)) (PreH8 : (i <= 47)) (PreH9 : (2 <= n0)) (PreH10 : (i <= (n0 + 1 ))) ,
  (IntArray.seg f 0 (fib_fill_len_z (n0) (i)) (fib_prefix_z ((fib_fill_len_z (n0) (i)))) )
  **  (IntArray.undef_seg f (fib_fill_len_z (n0) (i)) 1000 )
|--
  “ (0 <= n0) ” 
  &&  “ (n0 <= 46) ” 
  &&  “ (problem_55_pre_z n0 ) ” 
  &&  “ (fib_safe_z n0 ) ” 
  &&  “ (f <> 0) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= n0) ” 
  &&  “ ((fib_fill_len_z (n0) (i)) = i) ”
  &&  (IntArray.seg f 0 i (fib_prefix_z (i)) )
  **  (IntArray.undef_seg f i 1000 )
) \/
(
forall (n0: Z) (i: Z) (f: Z) (PreH1 : (i <= n0)) (PreH2 : (0 <= n0)) (PreH3 : (n0 <= 46)) (PreH4 : (problem_55_pre_z n0 )) (PreH5 : (fib_safe_z n0 )) (PreH6 : (f <> 0)) (PreH7 : (2 <= i)) (PreH8 : (i <= 47)) (PreH9 : (2 <= n0)) (PreH10 : (i <= (n0 + 1 ))) ,
  (IntArray.seg f 0 (fib_fill_len_z (n0) (i)) (fib_prefix_z ((fib_fill_len_z (n0) (i)))) )
  **  (IntArray.undef_seg f (fib_fill_len_z (n0) (i)) 1000 )
|--
  “ ((fib_fill_len_z (n0) (i)) = i) ”
  &&  (IntArray.seg f 0 i (fib_prefix_z (i)) )
  **  (IntArray.undef_seg f i 1000 )
).

Definition fib_entail_wit_3_split_goal_1 := 
forall (n0: Z) (i: Z) (f: Z) (PreH1 : (i <= n0)) (PreH2 : (0 <= n0)) (PreH3 : (n0 <= 46)) (PreH4 : (problem_55_pre_z n0 )) (PreH5 : (fib_safe_z n0 )) (PreH6 : (f <> 0)) (PreH7 : (2 <= i)) (PreH8 : (i <= 47)) (PreH9 : (2 <= n0)) (PreH10 : (i <= (n0 + 1 ))) ,
  (IntArray.seg f 0 (fib_fill_len_z (n0) (i)) (fib_prefix_z ((fib_fill_len_z (n0) (i)))) )
  **  (IntArray.undef_seg f (fib_fill_len_z (n0) (i)) 1000 )
|--
  “ ((fib_fill_len_z (n0) (i)) = i) ”
.

Definition fib_entail_wit_3_split_goal_spatial := 
forall (n0: Z) (i: Z) (f: Z) (PreH1 : (i <= n0)) (PreH2 : (0 <= n0)) (PreH3 : (n0 <= 46)) (PreH4 : (problem_55_pre_z n0 )) (PreH5 : (fib_safe_z n0 )) (PreH6 : (f <> 0)) (PreH7 : (2 <= i)) (PreH8 : (i <= 47)) (PreH9 : (2 <= n0)) (PreH10 : (i <= (n0 + 1 ))) ,
  (IntArray.seg f 0 (fib_fill_len_z (n0) (i)) (fib_prefix_z ((fib_fill_len_z (n0) (i)))) )
  **  (IntArray.undef_seg f (fib_fill_len_z (n0) (i)) 1000 )
|--
  (IntArray.seg f 0 i (fib_prefix_z (i)) )
  **  (IntArray.undef_seg f i 1000 )
.

Definition fib_entail_wit_4 := 
(
forall (n0: Z) (f: Z) (i: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 46)) (PreH3 : (problem_55_pre_z n0 )) (PreH4 : (fib_safe_z n0 )) (PreH5 : (f <> 0)) (PreH6 : (2 <= i)) (PreH7 : (i <= n0)) (PreH8 : ((fib_fill_len_z (n0) (i)) = i)) ,
  (IntArray.seg f 0 (i + 1 ) (app ((fib_prefix_z (i))) ((cons (((Znth ((i - 1 ) - 0 ) (fib_prefix_z (i)) 0) + (Znth ((i - 2 ) - 0 ) (fib_prefix_z (i)) 0) )) ((@nil Z))))) )
  **  (IntArray.undef_seg f (i + 1 ) 1000 )
|--
  “ (0 <= n0) ” 
  &&  “ (n0 <= 46) ” 
  &&  “ (problem_55_pre_z n0 ) ” 
  &&  “ (fib_safe_z n0 ) ” 
  &&  “ (f <> 0) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= n0) ” 
  &&  “ ((Znth ((i - 1 ) - 0 ) (fib_prefix_z (i)) 0) = (fib_z ((i - 1 )))) ” 
  &&  “ ((Znth ((i - 2 ) - 0 ) (fib_prefix_z (i)) 0) = (fib_z ((i - 2 )))) ” 
  &&  “ ((fib_z (i)) = ((Znth ((i - 1 ) - 0 ) (fib_prefix_z (i)) 0) + (Znth ((i - 2 ) - 0 ) (fib_prefix_z (i)) 0) )) ”
  &&  (IntArray.seg f 0 (i + 1 ) (fib_prefix_z ((i + 1 ))) )
  **  (IntArray.undef_seg f (i + 1 ) 1000 )
) \/
(
forall (n0: Z) (f: Z) (i: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 46)) (PreH3 : (problem_55_pre_z n0 )) (PreH4 : (fib_safe_z n0 )) (PreH5 : (f <> 0)) (PreH6 : (2 <= i)) (PreH7 : (i <= n0)) (PreH8 : ((fib_fill_len_z (n0) (i)) = i)) ,
  TT && emp 
|--
  “ ((fib_z (i)) = ((Znth ((i - 1 ) - 0 ) (fib_prefix_z (i)) 0) + (Znth ((i - 2 ) - 0 ) (fib_prefix_z (i)) 0) )) ” 
  &&  “ ((Znth ((i - 2 ) - 0 ) (fib_prefix_z (i)) 0) = (fib_z ((i - 2 )))) ” 
  &&  “ ((Znth ((i - 1 ) - 0 ) (fib_prefix_z (i)) 0) = (fib_z ((i - 1 )))) ” 
  &&  “ ((app ((fib_prefix_z (i))) ((cons (((Znth ((i - 1 ) - 0 ) (fib_prefix_z (i)) 0) + (Znth ((i - 2 ) - 0 ) (fib_prefix_z (i)) 0) )) ((@nil Z))))) = (fib_prefix_z ((i + 1 )))) ”
  &&  emp
).

Definition fib_entail_wit_4_split_goal_1 := 
forall (n0: Z) (f: Z) (i: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 46)) (PreH3 : (problem_55_pre_z n0 )) (PreH4 : (fib_safe_z n0 )) (PreH5 : (f <> 0)) (PreH6 : (2 <= i)) (PreH7 : (i <= n0)) (PreH8 : ((fib_fill_len_z (n0) (i)) = i)) ,
  TT && emp 
|--
  “ ((fib_z (i)) = ((Znth ((i - 1 ) - 0 ) (fib_prefix_z (i)) 0) + (Znth ((i - 2 ) - 0 ) (fib_prefix_z (i)) 0) )) ”
.

Definition fib_entail_wit_4_split_goal_2 := 
forall (n0: Z) (f: Z) (i: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 46)) (PreH3 : (problem_55_pre_z n0 )) (PreH4 : (fib_safe_z n0 )) (PreH5 : (f <> 0)) (PreH6 : (2 <= i)) (PreH7 : (i <= n0)) (PreH8 : ((fib_fill_len_z (n0) (i)) = i)) ,
  TT && emp 
|--
  “ ((Znth ((i - 2 ) - 0 ) (fib_prefix_z (i)) 0) = (fib_z ((i - 2 )))) ”
.

Definition fib_entail_wit_4_split_goal_3 := 
forall (n0: Z) (f: Z) (i: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 46)) (PreH3 : (problem_55_pre_z n0 )) (PreH4 : (fib_safe_z n0 )) (PreH5 : (f <> 0)) (PreH6 : (2 <= i)) (PreH7 : (i <= n0)) (PreH8 : ((fib_fill_len_z (n0) (i)) = i)) ,
  TT && emp 
|--
  “ ((Znth ((i - 1 ) - 0 ) (fib_prefix_z (i)) 0) = (fib_z ((i - 1 )))) ”
.

Definition fib_entail_wit_4_split_goal_4 := 
forall (n0: Z) (f: Z) (i: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 46)) (PreH3 : (problem_55_pre_z n0 )) (PreH4 : (fib_safe_z n0 )) (PreH5 : (f <> 0)) (PreH6 : (2 <= i)) (PreH7 : (i <= n0)) (PreH8 : ((fib_fill_len_z (n0) (i)) = i)) ,
  TT && emp 
|--
  “ ((app ((fib_prefix_z (i))) ((cons (((Znth ((i - 1 ) - 0 ) (fib_prefix_z (i)) 0) + (Znth ((i - 2 ) - 0 ) (fib_prefix_z (i)) 0) )) ((@nil Z))))) = (fib_prefix_z ((i + 1 )))) ”
.

Definition fib_entail_wit_5 := 
forall (n0: Z) (f: Z) (i: Z) (a: Z) (b: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 46)) (PreH3 : (problem_55_pre_z n0 )) (PreH4 : (fib_safe_z n0 )) (PreH5 : (f <> 0)) (PreH6 : (2 <= i)) (PreH7 : (i <= n0)) (PreH8 : (a = (fib_z ((i - 1 ))))) (PreH9 : (b = (fib_z ((i - 2 ))))) (PreH10 : ((fib_z (i)) = (a + b ))) ,
  (IntArray.seg f 0 (i + 1 ) (fib_prefix_z ((i + 1 ))) )
  **  (IntArray.undef_seg f (i + 1 ) 1000 )
|--
  (“ (0 <= n0) ” 
  &&  “ (n0 <= 46) ” 
  &&  “ (problem_55_pre_z n0 ) ” 
  &&  “ (fib_safe_z n0 ) ” 
  &&  “ (f <> 0) ” 
  &&  “ (2 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= 47) ” 
  &&  “ (n0 < 2) ” 
  &&  “ ((i + 1 ) = 2) ”
  &&  (IntArray.seg f 0 (fib_fill_len_z (n0) ((i + 1 ))) (fib_prefix_z ((fib_fill_len_z (n0) ((i + 1 ))))) )
  **  (IntArray.undef_seg f (fib_fill_len_z (n0) ((i + 1 ))) 1000 ))
  ||
  (“ (0 <= n0) ” 
  &&  “ (n0 <= 46) ” 
  &&  “ (problem_55_pre_z n0 ) ” 
  &&  “ (fib_safe_z n0 ) ” 
  &&  “ (f <> 0) ” 
  &&  “ (2 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= 47) ” 
  &&  “ (2 <= n0) ” 
  &&  “ ((i + 1 ) <= (n0 + 1 )) ”
  &&  (IntArray.seg f 0 (fib_fill_len_z (n0) ((i + 1 ))) (fib_prefix_z ((fib_fill_len_z (n0) ((i + 1 ))))) )
  **  (IntArray.undef_seg f (fib_fill_len_z (n0) ((i + 1 ))) 1000 ))
.

Definition fib_entail_wit_6_1 := 
(
forall (n0: Z) (i: Z) (f: Z) (PreH1 : (i > n0)) (PreH2 : (0 <= n0)) (PreH3 : (n0 <= 46)) (PreH4 : (problem_55_pre_z n0 )) (PreH5 : (fib_safe_z n0 )) (PreH6 : (f <> 0)) (PreH7 : (2 <= i)) (PreH8 : (i <= 47)) (PreH9 : (2 <= n0)) (PreH10 : (i <= (n0 + 1 ))) ,
  (IntArray.seg f 0 (fib_fill_len_z (n0) (i)) (fib_prefix_z ((fib_fill_len_z (n0) (i)))) )
  **  (IntArray.undef_seg f (fib_fill_len_z (n0) (i)) 1000 )
|--
  “ (0 <= n0) ” 
  &&  “ (n0 <= 46) ” 
  &&  “ (problem_55_pre_z n0 ) ” 
  &&  “ (fib_safe_z n0 ) ” 
  &&  “ (f <> 0) ”
  &&  (IntArray.seg f 0 (fib_fill_len_z (n0) ((n0 + 1 ))) (fib_prefix_z ((fib_fill_len_z (n0) ((n0 + 1 ))))) )
  **  (IntArray.undef_seg f (fib_fill_len_z (n0) ((n0 + 1 ))) 1000 )
) \/
(
forall (n0: Z) (i: Z) (f: Z) (PreH1 : (i > n0)) (PreH2 : (0 <= n0)) (PreH3 : (n0 <= 46)) (PreH4 : (problem_55_pre_z n0 )) (PreH5 : (fib_safe_z n0 )) (PreH6 : (f <> 0)) (PreH7 : (2 <= i)) (PreH8 : (i <= 47)) (PreH9 : (2 <= n0)) (PreH10 : (i <= (n0 + 1 ))) ,
  (IntArray.seg f 0 (fib_fill_len_z (n0) (i)) (fib_prefix_z ((fib_fill_len_z (n0) (i)))) )
  **  (IntArray.undef_seg f (fib_fill_len_z (n0) (i)) 1000 )
|--
  (IntArray.seg f 0 (fib_fill_len_z (n0) ((n0 + 1 ))) (fib_prefix_z ((fib_fill_len_z (n0) ((n0 + 1 ))))) )
  **  (IntArray.undef_seg f (fib_fill_len_z (n0) ((n0 + 1 ))) 1000 )
).

Definition fib_entail_wit_6_1_split_goal_spatial := 
forall (n0: Z) (i: Z) (f: Z) (PreH1 : (i > n0)) (PreH2 : (0 <= n0)) (PreH3 : (n0 <= 46)) (PreH4 : (problem_55_pre_z n0 )) (PreH5 : (fib_safe_z n0 )) (PreH6 : (f <> 0)) (PreH7 : (2 <= i)) (PreH8 : (i <= 47)) (PreH9 : (2 <= n0)) (PreH10 : (i <= (n0 + 1 ))) ,
  (IntArray.seg f 0 (fib_fill_len_z (n0) (i)) (fib_prefix_z ((fib_fill_len_z (n0) (i)))) )
  **  (IntArray.undef_seg f (fib_fill_len_z (n0) (i)) 1000 )
|--
  (IntArray.seg f 0 (fib_fill_len_z (n0) ((n0 + 1 ))) (fib_prefix_z ((fib_fill_len_z (n0) ((n0 + 1 ))))) )
  **  (IntArray.undef_seg f (fib_fill_len_z (n0) ((n0 + 1 ))) 1000 )
.

Definition fib_entail_wit_6_2 := 
(
forall (n0: Z) (i: Z) (f: Z) (PreH1 : (i > n0)) (PreH2 : (0 <= n0)) (PreH3 : (n0 <= 46)) (PreH4 : (problem_55_pre_z n0 )) (PreH5 : (fib_safe_z n0 )) (PreH6 : (f <> 0)) (PreH7 : (2 <= i)) (PreH8 : (i <= 47)) (PreH9 : (n0 < 2)) (PreH10 : (i = 2)) ,
  (IntArray.seg f 0 (fib_fill_len_z (n0) (i)) (fib_prefix_z ((fib_fill_len_z (n0) (i)))) )
  **  (IntArray.undef_seg f (fib_fill_len_z (n0) (i)) 1000 )
|--
  “ (0 <= n0) ” 
  &&  “ (n0 <= 46) ” 
  &&  “ (problem_55_pre_z n0 ) ” 
  &&  “ (fib_safe_z n0 ) ” 
  &&  “ (f <> 0) ”
  &&  (IntArray.seg f 0 (fib_fill_len_z (n0) ((n0 + 1 ))) (fib_prefix_z ((fib_fill_len_z (n0) ((n0 + 1 ))))) )
  **  (IntArray.undef_seg f (fib_fill_len_z (n0) ((n0 + 1 ))) 1000 )
) \/
(
forall (n0: Z) (i: Z) (f: Z) (PreH1 : (i > n0)) (PreH2 : (0 <= n0)) (PreH3 : (n0 <= 46)) (PreH4 : (problem_55_pre_z n0 )) (PreH5 : (fib_safe_z n0 )) (PreH6 : (f <> 0)) (PreH7 : (2 <= i)) (PreH8 : (i <= 47)) (PreH9 : (n0 < 2)) (PreH10 : (i = 2)) ,
  (IntArray.seg f 0 (fib_fill_len_z (n0) (i)) (fib_prefix_z ((fib_fill_len_z (n0) (i)))) )
  **  (IntArray.undef_seg f (fib_fill_len_z (n0) (i)) 1000 )
|--
  (IntArray.seg f 0 (fib_fill_len_z (n0) ((n0 + 1 ))) (fib_prefix_z ((fib_fill_len_z (n0) ((n0 + 1 ))))) )
  **  (IntArray.undef_seg f (fib_fill_len_z (n0) ((n0 + 1 ))) 1000 )
).

Definition fib_entail_wit_6_2_split_goal_spatial := 
forall (n0: Z) (i: Z) (f: Z) (PreH1 : (i > n0)) (PreH2 : (0 <= n0)) (PreH3 : (n0 <= 46)) (PreH4 : (problem_55_pre_z n0 )) (PreH5 : (fib_safe_z n0 )) (PreH6 : (f <> 0)) (PreH7 : (2 <= i)) (PreH8 : (i <= 47)) (PreH9 : (n0 < 2)) (PreH10 : (i = 2)) ,
  (IntArray.seg f 0 (fib_fill_len_z (n0) (i)) (fib_prefix_z ((fib_fill_len_z (n0) (i)))) )
  **  (IntArray.undef_seg f (fib_fill_len_z (n0) (i)) 1000 )
|--
  (IntArray.seg f 0 (fib_fill_len_z (n0) ((n0 + 1 ))) (fib_prefix_z ((fib_fill_len_z (n0) ((n0 + 1 ))))) )
  **  (IntArray.undef_seg f (fib_fill_len_z (n0) ((n0 + 1 ))) 1000 )
.

Definition fib_entail_wit_7_1 := 
(
forall (n0: Z) (f: Z) (PreH1 : (n0 >= 2)) (PreH2 : (0 <= n0)) (PreH3 : (n0 <= 46)) (PreH4 : (problem_55_pre_z n0 )) (PreH5 : (fib_safe_z n0 )) (PreH6 : (f <> 0)) ,
  (IntArray.seg f 0 (fib_fill_len_z (n0) ((n0 + 1 ))) (fib_prefix_z ((fib_fill_len_z (n0) ((n0 + 1 ))))) )
  **  (IntArray.undef_seg f (fib_fill_len_z (n0) ((n0 + 1 ))) 1000 )
|--
  “ ((n0 + 1 ) = (fib_fill_len_z (n0) ((n0 + 1 )))) ” 
  &&  “ (n0 < (n0 + 1 )) ” 
  &&  “ (0 <= n0) ” 
  &&  “ (n0 <= 46) ” 
  &&  “ (problem_55_pre_z n0 ) ” 
  &&  “ (fib_safe_z n0 ) ” 
  &&  “ (f <> 0) ” 
  &&  “ ((n0 + 1 ) <= 1000) ”
  &&  (IntArray.seg f 0 (n0 + 1 ) (fib_prefix_z ((n0 + 1 ))) )
  **  (IntArray.undef_seg f (n0 + 1 ) 1000 )
) \/
(
forall (n0: Z) (f: Z) (PreH1 : (n0 >= 2)) (PreH2 : (0 <= n0)) (PreH3 : (n0 <= 46)) (PreH4 : (problem_55_pre_z n0 )) (PreH5 : (fib_safe_z n0 )) (PreH6 : (f <> 0)) ,
  (IntArray.seg f 0 (fib_fill_len_z (n0) ((n0 + 1 ))) (fib_prefix_z ((fib_fill_len_z (n0) ((n0 + 1 ))))) )
  **  (IntArray.undef_seg f (fib_fill_len_z (n0) ((n0 + 1 ))) 1000 )
|--
  “ ((n0 + 1 ) = (fib_fill_len_z (n0) ((n0 + 1 )))) ”
  &&  (IntArray.seg f 0 (n0 + 1 ) (fib_prefix_z ((n0 + 1 ))) )
  **  (IntArray.undef_seg f (n0 + 1 ) 1000 )
).

Definition fib_entail_wit_7_1_split_goal_1 := 
forall (n0: Z) (f: Z) (PreH1 : (n0 >= 2)) (PreH2 : (0 <= n0)) (PreH3 : (n0 <= 46)) (PreH4 : (problem_55_pre_z n0 )) (PreH5 : (fib_safe_z n0 )) (PreH6 : (f <> 0)) ,
  (IntArray.seg f 0 (fib_fill_len_z (n0) ((n0 + 1 ))) (fib_prefix_z ((fib_fill_len_z (n0) ((n0 + 1 ))))) )
  **  (IntArray.undef_seg f (fib_fill_len_z (n0) ((n0 + 1 ))) 1000 )
|--
  “ ((n0 + 1 ) = (fib_fill_len_z (n0) ((n0 + 1 )))) ”
.

Definition fib_entail_wit_7_1_split_goal_spatial := 
forall (n0: Z) (f: Z) (PreH1 : (n0 >= 2)) (PreH2 : (0 <= n0)) (PreH3 : (n0 <= 46)) (PreH4 : (problem_55_pre_z n0 )) (PreH5 : (fib_safe_z n0 )) (PreH6 : (f <> 0)) ,
  (IntArray.seg f 0 (fib_fill_len_z (n0) ((n0 + 1 ))) (fib_prefix_z ((fib_fill_len_z (n0) ((n0 + 1 ))))) )
  **  (IntArray.undef_seg f (fib_fill_len_z (n0) ((n0 + 1 ))) 1000 )
|--
  (IntArray.seg f 0 (n0 + 1 ) (fib_prefix_z ((n0 + 1 ))) )
  **  (IntArray.undef_seg f (n0 + 1 ) 1000 )
.

Definition fib_entail_wit_7_2 := 
(
forall (n0: Z) (f: Z) (PreH1 : (n0 < 2)) (PreH2 : (0 <= n0)) (PreH3 : (n0 <= 46)) (PreH4 : (problem_55_pre_z n0 )) (PreH5 : (fib_safe_z n0 )) (PreH6 : (f <> 0)) ,
  (IntArray.seg f 0 (fib_fill_len_z (n0) ((n0 + 1 ))) (fib_prefix_z ((fib_fill_len_z (n0) ((n0 + 1 ))))) )
  **  (IntArray.undef_seg f (fib_fill_len_z (n0) ((n0 + 1 ))) 1000 )
|--
  “ (2 = (fib_fill_len_z (n0) ((n0 + 1 )))) ” 
  &&  “ (n0 < 2) ” 
  &&  “ (0 <= n0) ” 
  &&  “ (n0 <= 46) ” 
  &&  “ (problem_55_pre_z n0 ) ” 
  &&  “ (fib_safe_z n0 ) ” 
  &&  “ (f <> 0) ” 
  &&  “ (2 <= 1000) ”
  &&  (IntArray.seg f 0 2 (fib_prefix_z (2)) )
  **  (IntArray.undef_seg f 2 1000 )
) \/
(
forall (n0: Z) (f: Z) (PreH1 : (n0 < 2)) (PreH2 : (0 <= n0)) (PreH3 : (n0 <= 46)) (PreH4 : (problem_55_pre_z n0 )) (PreH5 : (fib_safe_z n0 )) (PreH6 : (f <> 0)) ,
  (IntArray.seg f 0 (fib_fill_len_z (n0) ((n0 + 1 ))) (fib_prefix_z ((fib_fill_len_z (n0) ((n0 + 1 ))))) )
  **  (IntArray.undef_seg f (fib_fill_len_z (n0) ((n0 + 1 ))) 1000 )
|--
  “ (2 = (fib_fill_len_z (n0) ((n0 + 1 )))) ”
  &&  (IntArray.seg f 0 2 (fib_prefix_z (2)) )
  **  (IntArray.undef_seg f 2 1000 )
).

Definition fib_entail_wit_7_2_split_goal_1 := 
forall (n0: Z) (f: Z) (PreH1 : (n0 < 2)) (PreH2 : (0 <= n0)) (PreH3 : (n0 <= 46)) (PreH4 : (problem_55_pre_z n0 )) (PreH5 : (fib_safe_z n0 )) (PreH6 : (f <> 0)) ,
  (IntArray.seg f 0 (fib_fill_len_z (n0) ((n0 + 1 ))) (fib_prefix_z ((fib_fill_len_z (n0) ((n0 + 1 ))))) )
  **  (IntArray.undef_seg f (fib_fill_len_z (n0) ((n0 + 1 ))) 1000 )
|--
  “ (2 = (fib_fill_len_z (n0) ((n0 + 1 )))) ”
.

Definition fib_entail_wit_7_2_split_goal_spatial := 
forall (n0: Z) (f: Z) (PreH1 : (n0 < 2)) (PreH2 : (0 <= n0)) (PreH3 : (n0 <= 46)) (PreH4 : (problem_55_pre_z n0 )) (PreH5 : (fib_safe_z n0 )) (PreH6 : (f <> 0)) ,
  (IntArray.seg f 0 (fib_fill_len_z (n0) ((n0 + 1 ))) (fib_prefix_z ((fib_fill_len_z (n0) ((n0 + 1 ))))) )
  **  (IntArray.undef_seg f (fib_fill_len_z (n0) ((n0 + 1 ))) 1000 )
|--
  (IntArray.seg f 0 2 (fib_prefix_z (2)) )
  **  (IntArray.undef_seg f 2 1000 )
.

Definition fib_entail_wit_8 := 
(
forall (n0: Z) (filled: Z) (f: Z) (PreH1 : (filled = (fib_fill_len_z (n0) ((n0 + 1 ))))) (PreH2 : (n0 < filled)) (PreH3 : (0 <= n0)) (PreH4 : (n0 <= 46)) (PreH5 : (problem_55_pre_z n0 )) (PreH6 : (fib_safe_z n0 )) (PreH7 : (f <> 0)) (PreH8 : (filled <= 1000)) ,
  (IntArray.seg f 0 filled (fib_prefix_z (filled)) )
  **  (IntArray.undef_seg f filled 1000 )
|--
  “ ((Znth (n0 - 0 ) (fib_prefix_z (filled)) 0) = (fib_z (n0))) ” 
  &&  “ (filled = (fib_fill_len_z (n0) ((n0 + 1 )))) ” 
  &&  “ (n0 < filled) ” 
  &&  “ (0 <= n0) ” 
  &&  “ (n0 <= 46) ” 
  &&  “ (problem_55_pre_z n0 ) ” 
  &&  “ (fib_safe_z n0 ) ” 
  &&  “ (f <> 0) ” 
  &&  “ (filled <= 1000) ”
  &&  (IntArray.seg f 0 filled (fib_prefix_z (filled)) )
  **  (IntArray.undef_seg f filled 1000 )
) \/
(
forall (n0: Z) (filled: Z) (f: Z) (PreH1 : (filled = (fib_fill_len_z (n0) ((n0 + 1 ))))) (PreH2 : (n0 < filled)) (PreH3 : (0 <= n0)) (PreH4 : (n0 <= 46)) (PreH5 : (problem_55_pre_z n0 )) (PreH6 : (fib_safe_z n0 )) (PreH7 : (f <> 0)) (PreH8 : (filled <= 1000)) ,
  TT && emp 
|--
  “ ((Znth (n0 - 0 ) (fib_prefix_z (filled)) 0) = (fib_z (n0))) ”
  &&  emp
).

Definition fib_entail_wit_8_split_goal_1 := 
forall (n0: Z) (filled: Z) (f: Z) (PreH1 : (filled = (fib_fill_len_z (n0) ((n0 + 1 ))))) (PreH2 : (n0 < filled)) (PreH3 : (0 <= n0)) (PreH4 : (n0 <= 46)) (PreH5 : (problem_55_pre_z n0 )) (PreH6 : (fib_safe_z n0 )) (PreH7 : (f <> 0)) (PreH8 : (filled <= 1000)) ,
  TT && emp 
|--
  “ ((Znth (n0 - 0 ) (fib_prefix_z (filled)) 0) = (fib_z (n0))) ”
.

Definition fib_return_wit_1 := 
(
forall (n0: Z) (result: Z) (filled: Z) (f: Z) (PreH1 : (result = (fib_z (n0)))) (PreH2 : (filled = (fib_fill_len_z (n0) ((n0 + 1 ))))) (PreH3 : (n0 < filled)) (PreH4 : (0 <= n0)) (PreH5 : (n0 <= 46)) (PreH6 : (problem_55_pre_z n0 )) (PreH7 : (fib_safe_z n0 )) (PreH8 : (f <> 0)) (PreH9 : (filled <= 1000)) ,
  TT && emp 
|--
  “ (problem_55_spec_z n0 result ) ”
  &&  emp
) \/
(
forall (n0: Z) (result: Z) (filled: Z) (f: Z) (PreH1 : (result = (fib_z (n0)))) (PreH2 : (filled = (fib_fill_len_z (n0) ((n0 + 1 ))))) (PreH3 : (n0 < filled)) (PreH4 : (0 <= n0)) (PreH5 : (n0 <= 46)) (PreH6 : (problem_55_pre_z n0 )) (PreH7 : (fib_safe_z n0 )) (PreH8 : (f <> 0)) (PreH9 : (filled <= 1000)) ,
  TT && emp 
|--
  “ (problem_55_spec_z n0 result ) ”
  &&  emp
).

Definition fib_return_wit_1_split_goal_1 := 
forall (n0: Z) (result: Z) (filled: Z) (f: Z) (PreH1 : (result = (fib_z (n0)))) (PreH2 : (filled = (fib_fill_len_z (n0) ((n0 + 1 ))))) (PreH3 : (n0 < filled)) (PreH4 : (0 <= n0)) (PreH5 : (n0 <= 46)) (PreH6 : (problem_55_pre_z n0 )) (PreH7 : (fib_safe_z n0 )) (PreH8 : (f <> 0)) (PreH9 : (filled <= 1000)) ,
  TT && emp 
|--
  “ (problem_55_spec_z n0 result ) ”
.

Definition fib_partial_solve_wit_1_pure := 
forall (n_pre: Z) (n0: Z) (PreH1 : (n_pre = n0)) (PreH2 : (0 <= n0)) (PreH3 : (n0 <= 46)) (PreH4 : (problem_55_pre_z n0 )) (PreH5 : (fib_safe_z n0 )) ,
  ((( &( "f" ) )) # Ptr  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (1000 = 1000) ”
.

Definition fib_partial_solve_wit_1_aux := 
forall (n_pre: Z) (n0: Z) (PreH1 : (n_pre = n0)) (PreH2 : (0 <= n0)) (PreH3 : (n0 <= 46)) (PreH4 : (problem_55_pre_z n0 )) (PreH5 : (fib_safe_z n0 )) ,
  TT && emp 
|--
  “ (1000 = 1000) ” 
  &&  “ (n_pre = n0) ” 
  &&  “ (0 <= n0) ” 
  &&  “ (n0 <= 46) ” 
  &&  “ (problem_55_pre_z n0 ) ” 
  &&  “ (fib_safe_z n0 ) ”
  &&  emp
.

Definition fib_partial_solve_wit_1 := fib_partial_solve_wit_1_pure -> fib_partial_solve_wit_1_aux.

Definition fib_partial_solve_wit_2 := 
forall (n_pre: Z) (n0: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (n_pre = n0)) (PreH3 : (0 <= n0)) (PreH4 : (n0 <= 46)) (PreH5 : (problem_55_pre_z n0 )) (PreH6 : (fib_safe_z n0 )) ,
  (IntArray.undef_full retval 1000 )
|--
  “ (retval <> 0) ” 
  &&  “ (n_pre = n0) ” 
  &&  “ (0 <= n0) ” 
  &&  “ (n0 <= 46) ” 
  &&  “ (problem_55_pre_z n0 ) ” 
  &&  “ (fib_safe_z n0 ) ”
  &&  (((retval + (0 * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg retval 1 1000 )
.

Definition fib_partial_solve_wit_3 := 
forall (n_pre: Z) (n0: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (n_pre = n0)) (PreH3 : (0 <= n0)) (PreH4 : (n0 <= 46)) (PreH5 : (problem_55_pre_z n0 )) (PreH6 : (fib_safe_z n0 )) ,
  (((retval + (0 * sizeof(INT) ) )) # Int  |-> 0)
  **  (IntArray.undef_seg retval 1 1000 )
|--
  “ (retval <> 0) ” 
  &&  “ (n_pre = n0) ” 
  &&  “ (0 <= n0) ” 
  &&  “ (n0 <= 46) ” 
  &&  “ (problem_55_pre_z n0 ) ” 
  &&  “ (fib_safe_z n0 ) ”
  &&  (((retval + (1 * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg retval (1 + 1 ) 1000 )
  **  (((retval + (0 * sizeof(INT) ) )) # Int  |-> 0)
.

Definition fib_partial_solve_wit_4 := 
forall (n0: Z) (f: Z) (i: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 46)) (PreH3 : (problem_55_pre_z n0 )) (PreH4 : (fib_safe_z n0 )) (PreH5 : (f <> 0)) (PreH6 : (2 <= i)) (PreH7 : (i <= n0)) (PreH8 : ((fib_fill_len_z (n0) (i)) = i)) ,
  (IntArray.seg f 0 i (fib_prefix_z (i)) )
  **  (IntArray.undef_seg f i 1000 )
|--
  “ (0 <= n0) ” 
  &&  “ (n0 <= 46) ” 
  &&  “ (problem_55_pre_z n0 ) ” 
  &&  “ (fib_safe_z n0 ) ” 
  &&  “ (f <> 0) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= n0) ” 
  &&  “ ((fib_fill_len_z (n0) (i)) = i) ”
  &&  (((f + ((i - 1 ) * sizeof(INT) ) )) # Int  |-> (Znth ((i - 1 ) - 0 ) (fib_prefix_z (i)) 0))
  **  (IntArray.missing_i f (i - 1 ) 0 i (fib_prefix_z (i)) )
  **  (IntArray.undef_seg f i 1000 )
.

Definition fib_partial_solve_wit_5 := 
forall (n0: Z) (f: Z) (i: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 46)) (PreH3 : (problem_55_pre_z n0 )) (PreH4 : (fib_safe_z n0 )) (PreH5 : (f <> 0)) (PreH6 : (2 <= i)) (PreH7 : (i <= n0)) (PreH8 : ((fib_fill_len_z (n0) (i)) = i)) ,
  (IntArray.seg f 0 i (fib_prefix_z (i)) )
  **  (IntArray.undef_seg f i 1000 )
|--
  “ (0 <= n0) ” 
  &&  “ (n0 <= 46) ” 
  &&  “ (problem_55_pre_z n0 ) ” 
  &&  “ (fib_safe_z n0 ) ” 
  &&  “ (f <> 0) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= n0) ” 
  &&  “ ((fib_fill_len_z (n0) (i)) = i) ”
  &&  (((f + ((i - 2 ) * sizeof(INT) ) )) # Int  |-> (Znth ((i - 2 ) - 0 ) (fib_prefix_z (i)) 0))
  **  (IntArray.missing_i f (i - 2 ) 0 i (fib_prefix_z (i)) )
  **  (IntArray.undef_seg f i 1000 )
.

Definition fib_partial_solve_wit_6 := 
forall (n0: Z) (f: Z) (i: Z) (PreH1 : (0 <= n0)) (PreH2 : (n0 <= 46)) (PreH3 : (problem_55_pre_z n0 )) (PreH4 : (fib_safe_z n0 )) (PreH5 : (f <> 0)) (PreH6 : (2 <= i)) (PreH7 : (i <= n0)) (PreH8 : ((fib_fill_len_z (n0) (i)) = i)) ,
  (IntArray.seg f 0 i (fib_prefix_z (i)) )
  **  (IntArray.undef_seg f i 1000 )
|--
  “ (0 <= n0) ” 
  &&  “ (n0 <= 46) ” 
  &&  “ (problem_55_pre_z n0 ) ” 
  &&  “ (fib_safe_z n0 ) ” 
  &&  “ (f <> 0) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= n0) ” 
  &&  “ ((fib_fill_len_z (n0) (i)) = i) ”
  &&  (((f + (i * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg f (i + 1 ) 1000 )
  **  (IntArray.seg f 0 i (fib_prefix_z (i)) )
.

Definition fib_partial_solve_wit_7 := 
forall (n0: Z) (filled: Z) (f: Z) (PreH1 : (filled = (fib_fill_len_z (n0) ((n0 + 1 ))))) (PreH2 : (n0 < filled)) (PreH3 : (0 <= n0)) (PreH4 : (n0 <= 46)) (PreH5 : (problem_55_pre_z n0 )) (PreH6 : (fib_safe_z n0 )) (PreH7 : (f <> 0)) (PreH8 : (filled <= 1000)) ,
  (IntArray.seg f 0 filled (fib_prefix_z (filled)) )
  **  (IntArray.undef_seg f filled 1000 )
|--
  “ (filled = (fib_fill_len_z (n0) ((n0 + 1 )))) ” 
  &&  “ (n0 < filled) ” 
  &&  “ (0 <= n0) ” 
  &&  “ (n0 <= 46) ” 
  &&  “ (problem_55_pre_z n0 ) ” 
  &&  “ (fib_safe_z n0 ) ” 
  &&  “ (f <> 0) ” 
  &&  “ (filled <= 1000) ”
  &&  (((f + (n0 * sizeof(INT) ) )) # Int  |-> (Znth (n0 - 0 ) (fib_prefix_z (filled)) 0))
  **  (IntArray.missing_i f n0 0 filled (fib_prefix_z (filled)) )
  **  (IntArray.undef_seg f filled 1000 )
.

Definition fib_partial_solve_wit_8_pure := 
forall (n0: Z) (result: Z) (filled: Z) (f: Z) (PreH1 : (result = (fib_z (n0)))) (PreH2 : (filled = (fib_fill_len_z (n0) ((n0 + 1 ))))) (PreH3 : (n0 < filled)) (PreH4 : (0 <= n0)) (PreH5 : (n0 <= 46)) (PreH6 : (problem_55_pre_z n0 )) (PreH7 : (fib_safe_z n0 )) (PreH8 : (f <> 0)) (PreH9 : (filled <= 1000)) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "result" ) )) # Int  |-> result)
  **  ((( &( "filled" ) )) # Int  |-> filled)
  **  ((( &( "f" ) )) # Ptr  |-> f)
  **  (IntArray.seg f 0 filled (fib_prefix_z (filled)) )
  **  (IntArray.undef_seg f filled 1000 )
|--
  “ (f <> 0) ” 
  &&  “ (0 <= filled) ” 
  &&  “ (filled <= 1000) ” 
  &&  “ (1000 = 1000) ”
.

Definition fib_partial_solve_wit_8_aux := 
forall (n0: Z) (result: Z) (filled: Z) (f: Z) (PreH1 : (result = (fib_z (n0)))) (PreH2 : (filled = (fib_fill_len_z (n0) ((n0 + 1 ))))) (PreH3 : (n0 < filled)) (PreH4 : (0 <= n0)) (PreH5 : (n0 <= 46)) (PreH6 : (problem_55_pre_z n0 )) (PreH7 : (fib_safe_z n0 )) (PreH8 : (f <> 0)) (PreH9 : (filled <= 1000)) ,
  (IntArray.seg f 0 filled (fib_prefix_z (filled)) )
  **  (IntArray.undef_seg f filled 1000 )
|--
  “ (f <> 0) ” 
  &&  “ (0 <= filled) ” 
  &&  “ (filled <= 1000) ” 
  &&  “ (1000 = 1000) ” 
  &&  “ (result = (fib_z (n0))) ” 
  &&  “ (filled = (fib_fill_len_z (n0) ((n0 + 1 )))) ” 
  &&  “ (n0 < filled) ” 
  &&  “ (0 <= n0) ” 
  &&  “ (n0 <= 46) ” 
  &&  “ (problem_55_pre_z n0 ) ” 
  &&  “ (fib_safe_z n0 ) ” 
  &&  “ (f <> 0) ” 
  &&  “ (filled <= 1000) ”
  &&  (IntArray.seg f 0 filled (fib_prefix_z (filled)) )
  **  (IntArray.undef_seg f filled 1000 )
.

Definition fib_partial_solve_wit_8 := fib_partial_solve_wit_8_pure -> fib_partial_solve_wit_8_aux.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_fib_safety_wit_1 : fib_safety_wit_1.
Axiom proof_of_fib_safety_wit_2 : fib_safety_wit_2.
Axiom proof_of_fib_safety_wit_3 : fib_safety_wit_3.
Axiom proof_of_fib_safety_wit_4 : fib_safety_wit_4.
Axiom proof_of_fib_safety_wit_5 : fib_safety_wit_5.
Axiom proof_of_fib_safety_wit_6 : fib_safety_wit_6.
Axiom proof_of_fib_safety_wit_7 : fib_safety_wit_7.
Axiom proof_of_fib_safety_wit_8 : fib_safety_wit_8.
Axiom proof_of_fib_safety_wit_9 : fib_safety_wit_9.
Axiom proof_of_fib_safety_wit_10 : fib_safety_wit_10.
Axiom proof_of_fib_safety_wit_11 : fib_safety_wit_11.
Axiom proof_of_fib_safety_wit_12 : fib_safety_wit_12.
Axiom proof_of_fib_safety_wit_13 : fib_safety_wit_13.
Axiom proof_of_fib_safety_wit_14 : fib_safety_wit_14.
Axiom proof_of_fib_safety_wit_15 : fib_safety_wit_15.
Axiom proof_of_fib_safety_wit_16 : fib_safety_wit_16.
Axiom proof_of_fib_safety_wit_17 : fib_safety_wit_17.
Axiom proof_of_fib_safety_wit_18 : fib_safety_wit_18.
Axiom proof_of_fib_entail_wit_1 : fib_entail_wit_1.
Axiom proof_of_fib_entail_wit_2 : fib_entail_wit_2.
Axiom proof_of_fib_entail_wit_3 : fib_entail_wit_3.
Axiom proof_of_fib_entail_wit_4 : fib_entail_wit_4.
Axiom proof_of_fib_entail_wit_5 : fib_entail_wit_5.
Axiom proof_of_fib_entail_wit_6_1 : fib_entail_wit_6_1.
Axiom proof_of_fib_entail_wit_6_2 : fib_entail_wit_6_2.
Axiom proof_of_fib_entail_wit_7_1 : fib_entail_wit_7_1.
Axiom proof_of_fib_entail_wit_7_2 : fib_entail_wit_7_2.
Axiom proof_of_fib_entail_wit_8 : fib_entail_wit_8.
Axiom proof_of_fib_return_wit_1 : fib_return_wit_1.
Axiom proof_of_fib_partial_solve_wit_1_pure : fib_partial_solve_wit_1_pure.
Axiom proof_of_fib_partial_solve_wit_1 : fib_partial_solve_wit_1.
Axiom proof_of_fib_partial_solve_wit_2 : fib_partial_solve_wit_2.
Axiom proof_of_fib_partial_solve_wit_3 : fib_partial_solve_wit_3.
Axiom proof_of_fib_partial_solve_wit_4 : fib_partial_solve_wit_4.
Axiom proof_of_fib_partial_solve_wit_5 : fib_partial_solve_wit_5.
Axiom proof_of_fib_partial_solve_wit_6 : fib_partial_solve_wit_6.
Axiom proof_of_fib_partial_solve_wit_7 : fib_partial_solve_wit_7.
Axiom proof_of_fib_partial_solve_wit_8_pure : fib_partial_solve_wit_8_pure.
Axiom proof_of_fib_partial_solve_wit_8 : fib_partial_solve_wit_8.

End VC_Correct.
