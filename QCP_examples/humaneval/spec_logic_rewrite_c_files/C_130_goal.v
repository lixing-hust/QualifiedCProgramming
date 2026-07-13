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
Require Import coins_130.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_proof.

(*----- Function tri -----*)

Definition tri_safety_wit_1 := 
forall (n_pre: Z) (n0: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (n_pre = n0)) (PreH3 : (0 <= n0)) (PreH4 : (n0 <= 1000)) (PreH5 : (problem_130_pre_z n0 )) (PreH6 : (tri_safe_z_130 n0 )) ,
  ((( &( "size" ) )) # Int  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((n_pre + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre + 1 )) ”
.

Definition tri_safety_wit_2 := 
forall (n_pre: Z) (n0: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (n_pre = n0)) (PreH3 : (0 <= n0)) (PreH4 : (n0 <= 1000)) (PreH5 : (problem_130_pre_z n0 )) (PreH6 : (tri_safe_z_130 n0 )) ,
  ((( &( "size" ) )) # Int  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition tri_safety_wit_3 := 
forall (n_pre: Z) (n0: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (n_pre = n0)) (PreH4 : (0 <= n0)) (PreH5 : (n0 <= 1000)) (PreH6 : (problem_130_pre_z n0 )) (PreH7 : (tri_safe_z_130 n0 )) ,
  (IntArray.undef_full retval_2 (n_pre + 1 ) )
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  ((( &( "size" ) )) # Int  |-> (n_pre + 1 ))
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (n_pre + 1 ))
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition tri_safety_wit_4 := 
forall (n_pre: Z) (n0: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (n_pre = n0)) (PreH4 : (0 <= n0)) (PreH5 : (n0 <= 1000)) (PreH6 : (problem_130_pre_z n0 )) (PreH7 : (tri_safe_z_130 n0 )) ,
  (IntArray.undef_full retval_2 (n_pre + 1 ) )
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  ((( &( "size" ) )) # Int  |-> (n_pre + 1 ))
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (n_pre + 1 ))
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition tri_safety_wit_5 := 
forall (n0: Z) (size: Z) (out: Z) (data: Z) (PreH1 : (size = (n0 + 1 ))) (PreH2 : (0 <= n0)) (PreH3 : (n0 <= 1000)) (PreH4 : (problem_130_pre_z n0 )) (PreH5 : (tri_safe_z_130 n0 )) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> size)
  **  (IntArray.seg data 0 1 (tri_prefix_z_130 (1)) )
  **  (IntArray.undef_seg data 1 size )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition tri_safety_wit_6 := 
forall (n0: Z) (size: Z) (out: Z) (data: Z) (PreH1 : (n0 <> 0)) (PreH2 : (size = (n0 + 1 ))) (PreH3 : (0 <= n0)) (PreH4 : (n0 <= 1000)) (PreH5 : (problem_130_pre_z n0 )) (PreH6 : (tri_safe_z_130 n0 )) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> size)
  **  (IntArray.seg data 0 1 (tri_prefix_z_130 (1)) )
  **  (IntArray.undef_seg data 1 size )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition tri_safety_wit_7 := 
forall (n0: Z) (size: Z) (out: Z) (data: Z) (PreH1 : (n0 <> 0)) (PreH2 : (size = (n0 + 1 ))) (PreH3 : (0 <= n0)) (PreH4 : (n0 <= 1000)) (PreH5 : (problem_130_pre_z n0 )) (PreH6 : (tri_safe_z_130 n0 )) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> size)
  **  (IntArray.seg data 0 1 (tri_prefix_z_130 (1)) )
  **  (IntArray.undef_seg data 1 size )
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition tri_safety_wit_8 := 
forall (n0: Z) (size: Z) (out: Z) (data: Z) (PreH1 : (n0 <> 0)) (PreH2 : (size = (n0 + 1 ))) (PreH3 : (0 <= n0)) (PreH4 : (n0 <= 1000)) (PreH5 : (problem_130_pre_z n0 )) (PreH6 : (tri_safe_z_130 n0 )) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  (IntArray.seg data 0 (1 + 1 ) (app ((tri_prefix_z_130 (1))) ((cons (3) ((@nil Z))))) )
  **  (IntArray.undef_seg data (1 + 1 ) size )
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> size)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition tri_safety_wit_9 := 
forall (n0: Z) (data: Z) (out: Z) (i: Z) (size: Z) (PreH1 : (i <= n0)) (PreH2 : (size = (n0 + 1 ))) (PreH3 : (1 <= n0)) (PreH4 : (n0 <= 1000)) (PreH5 : (problem_130_pre_z n0 )) (PreH6 : (tri_safe_z_130 n0 )) (PreH7 : (2 <= i)) (PreH8 : (i <= (n0 + 1 ))) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> size)
  **  (IntArray.seg data 0 i (tri_prefix_z_130 (i)) )
  **  (IntArray.undef_seg data i size )
|--
  “ ((i <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition tri_safety_wit_10 := 
forall (n0: Z) (data: Z) (out: Z) (i: Z) (size: Z) (PreH1 : (i <= n0)) (PreH2 : (size = (n0 + 1 ))) (PreH3 : (1 <= n0)) (PreH4 : (n0 <= 1000)) (PreH5 : (problem_130_pre_z n0 )) (PreH6 : (tri_safe_z_130 n0 )) (PreH7 : (2 <= i)) (PreH8 : (i <= (n0 + 1 ))) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> size)
  **  (IntArray.seg data 0 i (tri_prefix_z_130 (i)) )
  **  (IntArray.undef_seg data i size )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition tri_safety_wit_11 := 
forall (n0: Z) (data: Z) (out: Z) (i: Z) (size: Z) (PreH1 : (i <= n0)) (PreH2 : (size = (n0 + 1 ))) (PreH3 : (1 <= n0)) (PreH4 : (n0 <= 1000)) (PreH5 : (problem_130_pre_z n0 )) (PreH6 : (tri_safe_z_130 n0 )) (PreH7 : (2 <= i)) (PreH8 : (i <= (n0 + 1 ))) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> size)
  **  (IntArray.seg data 0 i (tri_prefix_z_130 (i)) )
  **  (IntArray.undef_seg data i size )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition tri_safety_wit_12 := 
(
forall (n0: Z) (data: Z) (out: Z) (i: Z) (size: Z) (PreH1 : ((i % ( 2 ) ) = 0)) (PreH2 : (i <= n0)) (PreH3 : (size = (n0 + 1 ))) (PreH4 : (1 <= n0)) (PreH5 : (n0 <= 1000)) (PreH6 : (problem_130_pre_z n0 )) (PreH7 : (tri_safe_z_130 n0 )) (PreH8 : (2 <= i)) (PreH9 : (i <= (n0 + 1 ))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> size)
  **  (IntArray.seg data 0 i (tri_prefix_z_130 (i)) )
  **  (IntArray.undef_seg data i size )
|--
  “ ((1 + (i ÷ 2 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (1 + (i ÷ 2 ) )) ”
) \/
(
forall (n0: Z) (data: Z) (out: Z) (i: Z) (size: Z) (PreH1 : ((i % ( 2 ) ) = 0)) (PreH2 : (i <= n0)) (PreH3 : (size = (n0 + 1 ))) (PreH4 : (1 <= n0)) (PreH5 : (n0 <= 1000)) (PreH6 : (problem_130_pre_z n0 )) (PreH7 : (tri_safe_z_130 n0 )) (PreH8 : (2 <= i)) (PreH9 : (i <= (n0 + 1 ))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> size)
  **  (IntArray.seg data 0 i (tri_prefix_z_130 (i)) )
  **  (IntArray.undef_seg data i size )
|--
  “ ((1 + (i ÷ 2 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (1 + (i ÷ 2 ) )) ”
).

Definition tri_safety_wit_12_split_goal_1 := 
forall (n0: Z) (data: Z) (out: Z) (i: Z) (size: Z) (PreH1 : ((i % ( 2 ) ) = 0)) (PreH2 : (i <= n0)) (PreH3 : (size = (n0 + 1 ))) (PreH4 : (1 <= n0)) (PreH5 : (n0 <= 1000)) (PreH6 : (problem_130_pre_z n0 )) (PreH7 : (tri_safe_z_130 n0 )) (PreH8 : (2 <= i)) (PreH9 : (i <= (n0 + 1 ))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> size)
  **  (IntArray.seg data 0 i (tri_prefix_z_130 (i)) )
  **  (IntArray.undef_seg data i size )
|--
  “ ((1 + (i ÷ 2 ) ) <= INT_MAX) ”
.

Definition tri_safety_wit_12_split_goal_2 := 
forall (n0: Z) (data: Z) (out: Z) (i: Z) (size: Z) (PreH1 : ((i % ( 2 ) ) = 0)) (PreH2 : (i <= n0)) (PreH3 : (size = (n0 + 1 ))) (PreH4 : (1 <= n0)) (PreH5 : (n0 <= 1000)) (PreH6 : (problem_130_pre_z n0 )) (PreH7 : (tri_safe_z_130 n0 )) (PreH8 : (2 <= i)) (PreH9 : (i <= (n0 + 1 ))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> size)
  **  (IntArray.seg data 0 i (tri_prefix_z_130 (i)) )
  **  (IntArray.undef_seg data i size )
|--
  “ ((INT_MIN) <= (1 + (i ÷ 2 ) )) ”
.

Definition tri_safety_wit_13 := 
forall (n0: Z) (data: Z) (out: Z) (i: Z) (size: Z) (PreH1 : ((i % ( 2 ) ) = 0)) (PreH2 : (i <= n0)) (PreH3 : (size = (n0 + 1 ))) (PreH4 : (1 <= n0)) (PreH5 : (n0 <= 1000)) (PreH6 : (problem_130_pre_z n0 )) (PreH7 : (tri_safe_z_130 n0 )) (PreH8 : (2 <= i)) (PreH9 : (i <= (n0 + 1 ))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> size)
  **  (IntArray.seg data 0 i (tri_prefix_z_130 (i)) )
  **  (IntArray.undef_seg data i size )
|--
  “ ((i <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition tri_safety_wit_14 := 
forall (n0: Z) (data: Z) (out: Z) (i: Z) (size: Z) (PreH1 : ((i % ( 2 ) ) = 0)) (PreH2 : (i <= n0)) (PreH3 : (size = (n0 + 1 ))) (PreH4 : (1 <= n0)) (PreH5 : (n0 <= 1000)) (PreH6 : (problem_130_pre_z n0 )) (PreH7 : (tri_safe_z_130 n0 )) (PreH8 : (2 <= i)) (PreH9 : (i <= (n0 + 1 ))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> size)
  **  (IntArray.seg data 0 i (tri_prefix_z_130 (i)) )
  **  (IntArray.undef_seg data i size )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition tri_safety_wit_15 := 
forall (n0: Z) (data: Z) (out: Z) (i: Z) (size: Z) (PreH1 : ((i % ( 2 ) ) = 0)) (PreH2 : (i <= n0)) (PreH3 : (size = (n0 + 1 ))) (PreH4 : (1 <= n0)) (PreH5 : (n0 <= 1000)) (PreH6 : (problem_130_pre_z n0 )) (PreH7 : (tri_safe_z_130 n0 )) (PreH8 : (2 <= i)) (PreH9 : (i <= (n0 + 1 ))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> size)
  **  (IntArray.seg data 0 i (tri_prefix_z_130 (i)) )
  **  (IntArray.undef_seg data i size )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition tri_safety_wit_16 := 
(
forall (n0: Z) (data: Z) (out: Z) (i: Z) (size: Z) (PreH1 : ((i % ( 2 ) ) <> 0)) (PreH2 : (i <= n0)) (PreH3 : (size = (n0 + 1 ))) (PreH4 : (1 <= n0)) (PreH5 : (n0 <= 1000)) (PreH6 : (problem_130_pre_z n0 )) (PreH7 : (tri_safe_z_130 n0 )) (PreH8 : (2 <= i)) (PreH9 : (i <= (n0 + 1 ))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) ,
  (IntArray.seg data 0 i (tri_prefix_z_130 (i)) )
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> size)
  **  (IntArray.undef_seg data i size )
|--
  “ (((((Znth ((i - 1 ) - 0 ) (tri_prefix_z_130 (i)) 0) + (Znth ((i - 2 ) - 0 ) (tri_prefix_z_130 (i)) 0) ) + 1 ) + ((i + 1 ) ÷ 2 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((((Znth ((i - 1 ) - 0 ) (tri_prefix_z_130 (i)) 0) + (Znth ((i - 2 ) - 0 ) (tri_prefix_z_130 (i)) 0) ) + 1 ) + ((i + 1 ) ÷ 2 ) )) ”
) \/
(
forall (n0: Z) (data: Z) (out: Z) (i: Z) (size: Z) (PreH1 : ((i % ( 2 ) ) <> 0)) (PreH2 : (i <= n0)) (PreH3 : (size = (n0 + 1 ))) (PreH4 : (1 <= n0)) (PreH5 : (n0 <= 1000)) (PreH6 : (problem_130_pre_z n0 )) (PreH7 : (tri_safe_z_130 n0 )) (PreH8 : (2 <= i)) (PreH9 : (i <= (n0 + 1 ))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) ,
  (IntArray.seg data 0 i (tri_prefix_z_130 (i)) )
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> size)
  **  (IntArray.undef_seg data i size )
|--
  “ (((((Znth ((i - 1 ) - 0 ) (tri_prefix_z_130 (i)) 0) + (Znth ((i - 2 ) - 0 ) (tri_prefix_z_130 (i)) 0) ) + 1 ) + ((i + 1 ) ÷ 2 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((((Znth ((i - 1 ) - 0 ) (tri_prefix_z_130 (i)) 0) + (Znth ((i - 2 ) - 0 ) (tri_prefix_z_130 (i)) 0) ) + 1 ) + ((i + 1 ) ÷ 2 ) )) ”
).

Definition tri_safety_wit_16_split_goal_1 := 
forall (n0: Z) (data: Z) (out: Z) (i: Z) (size: Z) (PreH1 : ((i % ( 2 ) ) <> 0)) (PreH2 : (i <= n0)) (PreH3 : (size = (n0 + 1 ))) (PreH4 : (1 <= n0)) (PreH5 : (n0 <= 1000)) (PreH6 : (problem_130_pre_z n0 )) (PreH7 : (tri_safe_z_130 n0 )) (PreH8 : (2 <= i)) (PreH9 : (i <= (n0 + 1 ))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) ,
  (IntArray.seg data 0 i (tri_prefix_z_130 (i)) )
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> size)
  **  (IntArray.undef_seg data i size )
|--
  “ (((((Znth ((i - 1 ) - 0 ) (tri_prefix_z_130 (i)) 0) + (Znth ((i - 2 ) - 0 ) (tri_prefix_z_130 (i)) 0) ) + 1 ) + ((i + 1 ) ÷ 2 ) ) <= INT_MAX) ”
.

Definition tri_safety_wit_16_split_goal_2 := 
forall (n0: Z) (data: Z) (out: Z) (i: Z) (size: Z) (PreH1 : ((i % ( 2 ) ) <> 0)) (PreH2 : (i <= n0)) (PreH3 : (size = (n0 + 1 ))) (PreH4 : (1 <= n0)) (PreH5 : (n0 <= 1000)) (PreH6 : (problem_130_pre_z n0 )) (PreH7 : (tri_safe_z_130 n0 )) (PreH8 : (2 <= i)) (PreH9 : (i <= (n0 + 1 ))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) ,
  (IntArray.seg data 0 i (tri_prefix_z_130 (i)) )
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> size)
  **  (IntArray.undef_seg data i size )
|--
  “ ((INT_MIN) <= ((((Znth ((i - 1 ) - 0 ) (tri_prefix_z_130 (i)) 0) + (Znth ((i - 2 ) - 0 ) (tri_prefix_z_130 (i)) 0) ) + 1 ) + ((i + 1 ) ÷ 2 ) )) ”
.

Definition tri_safety_wit_17 := 
forall (n0: Z) (data: Z) (out: Z) (i: Z) (size: Z) (PreH1 : ((i % ( 2 ) ) <> 0)) (PreH2 : (i <= n0)) (PreH3 : (size = (n0 + 1 ))) (PreH4 : (1 <= n0)) (PreH5 : (n0 <= 1000)) (PreH6 : (problem_130_pre_z n0 )) (PreH7 : (tri_safe_z_130 n0 )) (PreH8 : (2 <= i)) (PreH9 : (i <= (n0 + 1 ))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) ,
  (IntArray.seg data 0 i (tri_prefix_z_130 (i)) )
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> size)
  **  (IntArray.undef_seg data i size )
|--
  “ (((i + 1 ) <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition tri_safety_wit_18 := 
forall (n0: Z) (data: Z) (out: Z) (i: Z) (size: Z) (PreH1 : ((i % ( 2 ) ) <> 0)) (PreH2 : (i <= n0)) (PreH3 : (size = (n0 + 1 ))) (PreH4 : (1 <= n0)) (PreH5 : (n0 <= 1000)) (PreH6 : (problem_130_pre_z n0 )) (PreH7 : (tri_safe_z_130 n0 )) (PreH8 : (2 <= i)) (PreH9 : (i <= (n0 + 1 ))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) ,
  (IntArray.seg data 0 i (tri_prefix_z_130 (i)) )
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> size)
  **  (IntArray.undef_seg data i size )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition tri_safety_wit_19 := 
(
forall (n0: Z) (data: Z) (out: Z) (i: Z) (size: Z) (PreH1 : ((i % ( 2 ) ) <> 0)) (PreH2 : (i <= n0)) (PreH3 : (size = (n0 + 1 ))) (PreH4 : (1 <= n0)) (PreH5 : (n0 <= 1000)) (PreH6 : (problem_130_pre_z n0 )) (PreH7 : (tri_safe_z_130 n0 )) (PreH8 : (2 <= i)) (PreH9 : (i <= (n0 + 1 ))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) ,
  (IntArray.seg data 0 i (tri_prefix_z_130 (i)) )
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> size)
  **  (IntArray.undef_seg data i size )
|--
  “ ((((Znth ((i - 1 ) - 0 ) (tri_prefix_z_130 (i)) 0) + (Znth ((i - 2 ) - 0 ) (tri_prefix_z_130 (i)) 0) ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((Znth ((i - 1 ) - 0 ) (tri_prefix_z_130 (i)) 0) + (Znth ((i - 2 ) - 0 ) (tri_prefix_z_130 (i)) 0) ) + 1 )) ”
) \/
(
forall (n0: Z) (data: Z) (out: Z) (i: Z) (size: Z) (PreH1 : ((i % ( 2 ) ) <> 0)) (PreH2 : (i <= n0)) (PreH3 : (size = (n0 + 1 ))) (PreH4 : (1 <= n0)) (PreH5 : (n0 <= 1000)) (PreH6 : (problem_130_pre_z n0 )) (PreH7 : (tri_safe_z_130 n0 )) (PreH8 : (2 <= i)) (PreH9 : (i <= (n0 + 1 ))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) ,
  (IntArray.seg data 0 i (tri_prefix_z_130 (i)) )
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> size)
  **  (IntArray.undef_seg data i size )
|--
  “ ((((Znth ((i - 1 ) - 0 ) (tri_prefix_z_130 (i)) 0) + (Znth ((i - 2 ) - 0 ) (tri_prefix_z_130 (i)) 0) ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((Znth ((i - 1 ) - 0 ) (tri_prefix_z_130 (i)) 0) + (Znth ((i - 2 ) - 0 ) (tri_prefix_z_130 (i)) 0) ) + 1 )) ”
).

Definition tri_safety_wit_19_split_goal_1 := 
forall (n0: Z) (data: Z) (out: Z) (i: Z) (size: Z) (PreH1 : ((i % ( 2 ) ) <> 0)) (PreH2 : (i <= n0)) (PreH3 : (size = (n0 + 1 ))) (PreH4 : (1 <= n0)) (PreH5 : (n0 <= 1000)) (PreH6 : (problem_130_pre_z n0 )) (PreH7 : (tri_safe_z_130 n0 )) (PreH8 : (2 <= i)) (PreH9 : (i <= (n0 + 1 ))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) ,
  (IntArray.seg data 0 i (tri_prefix_z_130 (i)) )
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> size)
  **  (IntArray.undef_seg data i size )
|--
  “ ((((Znth ((i - 1 ) - 0 ) (tri_prefix_z_130 (i)) 0) + (Znth ((i - 2 ) - 0 ) (tri_prefix_z_130 (i)) 0) ) + 1 ) <= INT_MAX) ”
.

Definition tri_safety_wit_19_split_goal_2 := 
forall (n0: Z) (data: Z) (out: Z) (i: Z) (size: Z) (PreH1 : ((i % ( 2 ) ) <> 0)) (PreH2 : (i <= n0)) (PreH3 : (size = (n0 + 1 ))) (PreH4 : (1 <= n0)) (PreH5 : (n0 <= 1000)) (PreH6 : (problem_130_pre_z n0 )) (PreH7 : (tri_safe_z_130 n0 )) (PreH8 : (2 <= i)) (PreH9 : (i <= (n0 + 1 ))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) ,
  (IntArray.seg data 0 i (tri_prefix_z_130 (i)) )
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> size)
  **  (IntArray.undef_seg data i size )
|--
  “ ((INT_MIN) <= (((Znth ((i - 1 ) - 0 ) (tri_prefix_z_130 (i)) 0) + (Znth ((i - 2 ) - 0 ) (tri_prefix_z_130 (i)) 0) ) + 1 )) ”
.

Definition tri_safety_wit_20 := 
(
forall (n0: Z) (data: Z) (out: Z) (i: Z) (size: Z) (PreH1 : ((i % ( 2 ) ) <> 0)) (PreH2 : (i <= n0)) (PreH3 : (size = (n0 + 1 ))) (PreH4 : (1 <= n0)) (PreH5 : (n0 <= 1000)) (PreH6 : (problem_130_pre_z n0 )) (PreH7 : (tri_safe_z_130 n0 )) (PreH8 : (2 <= i)) (PreH9 : (i <= (n0 + 1 ))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) ,
  (IntArray.seg data 0 i (tri_prefix_z_130 (i)) )
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> size)
  **  (IntArray.undef_seg data i size )
|--
  “ (((Znth ((i - 1 ) - 0 ) (tri_prefix_z_130 (i)) 0) + (Znth ((i - 2 ) - 0 ) (tri_prefix_z_130 (i)) 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth ((i - 1 ) - 0 ) (tri_prefix_z_130 (i)) 0) + (Znth ((i - 2 ) - 0 ) (tri_prefix_z_130 (i)) 0) )) ”
) \/
(
forall (n0: Z) (data: Z) (out: Z) (i: Z) (size: Z) (PreH1 : ((i % ( 2 ) ) <> 0)) (PreH2 : (i <= n0)) (PreH3 : (size = (n0 + 1 ))) (PreH4 : (1 <= n0)) (PreH5 : (n0 <= 1000)) (PreH6 : (problem_130_pre_z n0 )) (PreH7 : (tri_safe_z_130 n0 )) (PreH8 : (2 <= i)) (PreH9 : (i <= (n0 + 1 ))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) ,
  (IntArray.seg data 0 i (tri_prefix_z_130 (i)) )
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> size)
  **  (IntArray.undef_seg data i size )
|--
  “ (((Znth ((i - 1 ) - 0 ) (tri_prefix_z_130 (i)) 0) + (Znth ((i - 2 ) - 0 ) (tri_prefix_z_130 (i)) 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth ((i - 1 ) - 0 ) (tri_prefix_z_130 (i)) 0) + (Znth ((i - 2 ) - 0 ) (tri_prefix_z_130 (i)) 0) )) ”
).

Definition tri_safety_wit_20_split_goal_1 := 
forall (n0: Z) (data: Z) (out: Z) (i: Z) (size: Z) (PreH1 : ((i % ( 2 ) ) <> 0)) (PreH2 : (i <= n0)) (PreH3 : (size = (n0 + 1 ))) (PreH4 : (1 <= n0)) (PreH5 : (n0 <= 1000)) (PreH6 : (problem_130_pre_z n0 )) (PreH7 : (tri_safe_z_130 n0 )) (PreH8 : (2 <= i)) (PreH9 : (i <= (n0 + 1 ))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) ,
  (IntArray.seg data 0 i (tri_prefix_z_130 (i)) )
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> size)
  **  (IntArray.undef_seg data i size )
|--
  “ (((Znth ((i - 1 ) - 0 ) (tri_prefix_z_130 (i)) 0) + (Znth ((i - 2 ) - 0 ) (tri_prefix_z_130 (i)) 0) ) <= INT_MAX) ”
.

Definition tri_safety_wit_20_split_goal_2 := 
forall (n0: Z) (data: Z) (out: Z) (i: Z) (size: Z) (PreH1 : ((i % ( 2 ) ) <> 0)) (PreH2 : (i <= n0)) (PreH3 : (size = (n0 + 1 ))) (PreH4 : (1 <= n0)) (PreH5 : (n0 <= 1000)) (PreH6 : (problem_130_pre_z n0 )) (PreH7 : (tri_safe_z_130 n0 )) (PreH8 : (2 <= i)) (PreH9 : (i <= (n0 + 1 ))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) ,
  (IntArray.seg data 0 i (tri_prefix_z_130 (i)) )
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> size)
  **  (IntArray.undef_seg data i size )
|--
  “ ((INT_MIN) <= ((Znth ((i - 1 ) - 0 ) (tri_prefix_z_130 (i)) 0) + (Znth ((i - 2 ) - 0 ) (tri_prefix_z_130 (i)) 0) )) ”
.

Definition tri_safety_wit_21 := 
forall (n0: Z) (data: Z) (out: Z) (i: Z) (size: Z) (PreH1 : ((i % ( 2 ) ) <> 0)) (PreH2 : (i <= n0)) (PreH3 : (size = (n0 + 1 ))) (PreH4 : (1 <= n0)) (PreH5 : (n0 <= 1000)) (PreH6 : (problem_130_pre_z n0 )) (PreH7 : (tri_safe_z_130 n0 )) (PreH8 : (2 <= i)) (PreH9 : (i <= (n0 + 1 ))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) ,
  (IntArray.seg data 0 i (tri_prefix_z_130 (i)) )
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> size)
  **  (IntArray.undef_seg data i size )
|--
  “ ((i - 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 2 )) ”
.

Definition tri_safety_wit_22 := 
forall (n0: Z) (data: Z) (out: Z) (i: Z) (size: Z) (PreH1 : ((i % ( 2 ) ) <> 0)) (PreH2 : (i <= n0)) (PreH3 : (size = (n0 + 1 ))) (PreH4 : (1 <= n0)) (PreH5 : (n0 <= 1000)) (PreH6 : (problem_130_pre_z n0 )) (PreH7 : (tri_safe_z_130 n0 )) (PreH8 : (2 <= i)) (PreH9 : (i <= (n0 + 1 ))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> size)
  **  (IntArray.seg data 0 i (tri_prefix_z_130 (i)) )
  **  (IntArray.undef_seg data i size )
|--
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition tri_safety_wit_23 := 
forall (n0: Z) (data: Z) (out: Z) (i: Z) (size: Z) (PreH1 : ((i % ( 2 ) ) <> 0)) (PreH2 : (i <= n0)) (PreH3 : (size = (n0 + 1 ))) (PreH4 : (1 <= n0)) (PreH5 : (n0 <= 1000)) (PreH6 : (problem_130_pre_z n0 )) (PreH7 : (tri_safe_z_130 n0 )) (PreH8 : (2 <= i)) (PreH9 : (i <= (n0 + 1 ))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> size)
  **  (IntArray.seg data 0 i (tri_prefix_z_130 (i)) )
  **  (IntArray.undef_seg data i size )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition tri_safety_wit_24 := 
forall (n0: Z) (data: Z) (out: Z) (i: Z) (size: Z) (PreH1 : ((i % ( 2 ) ) <> 0)) (PreH2 : (i <= n0)) (PreH3 : (size = (n0 + 1 ))) (PreH4 : (1 <= n0)) (PreH5 : (n0 <= 1000)) (PreH6 : (problem_130_pre_z n0 )) (PreH7 : (tri_safe_z_130 n0 )) (PreH8 : (2 <= i)) (PreH9 : (i <= (n0 + 1 ))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) ,
  (IntArray.seg data 0 i (tri_prefix_z_130 (i)) )
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> size)
  **  (IntArray.undef_seg data i size )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition tri_safety_wit_25 := 
forall (n0: Z) (data: Z) (out: Z) (i: Z) (size: Z) (PreH1 : ((i % ( 2 ) ) <> 0)) (PreH2 : (i <= n0)) (PreH3 : (size = (n0 + 1 ))) (PreH4 : (1 <= n0)) (PreH5 : (n0 <= 1000)) (PreH6 : (problem_130_pre_z n0 )) (PreH7 : (tri_safe_z_130 n0 )) (PreH8 : (2 <= i)) (PreH9 : (i <= (n0 + 1 ))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) ,
  (IntArray.seg data 0 i (tri_prefix_z_130 (i)) )
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> size)
  **  (IntArray.undef_seg data i size )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition tri_safety_wit_26 := 
forall (n0: Z) (data: Z) (out: Z) (i: Z) (size: Z) (PreH1 : ((i % ( 2 ) ) <> 0)) (PreH2 : (i <= n0)) (PreH3 : (size = (n0 + 1 ))) (PreH4 : (1 <= n0)) (PreH5 : (n0 <= 1000)) (PreH6 : (problem_130_pre_z n0 )) (PreH7 : (tri_safe_z_130 n0 )) (PreH8 : (2 <= i)) (PreH9 : (i <= (n0 + 1 ))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) ,
  (IntArray.seg data 0 i (tri_prefix_z_130 (i)) )
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> size)
  **  (IntArray.undef_seg data i size )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition tri_safety_wit_27 := 
forall (n0: Z) (data: Z) (out: Z) (i: Z) (size: Z) (PreH1 : ((i % ( 2 ) ) <> 0)) (PreH2 : (i <= n0)) (PreH3 : (size = (n0 + 1 ))) (PreH4 : (1 <= n0)) (PreH5 : (n0 <= 1000)) (PreH6 : (problem_130_pre_z n0 )) (PreH7 : (tri_safe_z_130 n0 )) (PreH8 : (2 <= i)) (PreH9 : (i <= (n0 + 1 ))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) ,
  (IntArray.seg data 0 i (tri_prefix_z_130 (i)) )
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> size)
  **  (IntArray.undef_seg data i size )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition tri_safety_wit_28 := 
forall (n0: Z) (size: Z) (i: Z) (out: Z) (data: Z) (PreH1 : (size = (n0 + 1 ))) (PreH2 : (1 <= n0)) (PreH3 : (n0 <= 1000)) (PreH4 : (problem_130_pre_z n0 )) (PreH5 : (tri_safe_z_130 n0 )) (PreH6 : (2 <= i)) (PreH7 : (i <= n0)) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> size)
  **  (IntArray.seg data 0 (i + 1 ) (tri_prefix_z_130 ((i + 1 ))) )
  **  (IntArray.undef_seg data (i + 1 ) size )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition tri_entail_wit_1 := 
(
forall (n_pre: Z) (n0: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (n_pre = n0)) (PreH4 : (0 <= n0)) (PreH5 : (n0 <= 1000)) (PreH6 : (problem_130_pre_z n0 )) (PreH7 : (tri_safe_z_130 n0 )) ,
  (((retval_2 + (0 * sizeof(INT) ) )) # Int  |-> 1)
  **  (IntArray.undef_seg retval_2 1 (n_pre + 1 ) )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (n_pre + 1 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((n_pre + 1 ) = (n0 + 1 )) ” 
  &&  “ (0 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_130_pre_z n0 ) ” 
  &&  “ (tri_safe_z_130 n0 ) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval_2 <> 0) ”
  &&  ((( &( "n" ) )) # Int  |-> n0)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (n_pre + 1 ))
  **  (IntArray.seg retval_2 0 1 (tri_prefix_z_130 (1)) )
  **  (IntArray.undef_seg retval_2 1 (n_pre + 1 ) )
) \/
(
forall (n_pre: Z) (n0: Z) (retval: Z) (retval_2: Z) (PreH1 : (1 <= INT_MAX)) (PreH2 : (1 >= INT_MIN)) (PreH3 : (retval_2 <> 0)) (PreH4 : (retval <> 0)) (PreH5 : (n_pre = n0)) (PreH6 : (0 <= n0)) (PreH7 : (n0 <= 1000)) (PreH8 : (problem_130_pre_z n0 )) (PreH9 : (tri_safe_z_130 n0 )) ,
  (((retval_2 + (0 * sizeof(INT) ) )) # Int  |-> 1)
|--
  (IntArray.seg retval_2 0 1 (tri_prefix_z_130 (1)) )
).

Definition tri_entail_wit_1_split_goal_spatial := 
forall (n_pre: Z) (n0: Z) (retval: Z) (retval_2: Z) (PreH1 : (1 <= INT_MAX)) (PreH2 : (1 >= INT_MIN)) (PreH3 : (retval_2 <> 0)) (PreH4 : (retval <> 0)) (PreH5 : (n_pre = n0)) (PreH6 : (0 <= n0)) (PreH7 : (n0 <= 1000)) (PreH8 : (problem_130_pre_z n0 )) (PreH9 : (tri_safe_z_130 n0 )) ,
  (((retval_2 + (0 * sizeof(INT) ) )) # Int  |-> 1)
|--
  (IntArray.seg retval_2 0 1 (tri_prefix_z_130 (1)) )
.

Definition tri_entail_wit_2 := 
(
forall (n0: Z) (size: Z) (out: Z) (data: Z) (PreH1 : (n0 = 0)) (PreH2 : (size = (n0 + 1 ))) (PreH3 : (0 <= n0)) (PreH4 : (n0 <= 1000)) (PreH5 : (problem_130_pre_z n0 )) (PreH6 : (tri_safe_z_130 n0 )) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> size)
  **  (IntArray.seg data 0 1 (tri_prefix_z_130 (1)) )
  **  (IntArray.undef_seg data 1 size )
|--
  “ (n0 = 0) ” 
  &&  “ (size = (n0 + 1 )) ” 
  &&  “ (problem_130_pre_z n0 ) ” 
  &&  “ (tri_safe_z_130 n0 ) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (problem_130_spec_z n0 (tri_prefix_z_130 ((n0 + 1 ))) ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (n0 + 1 ))
  **  (IntArray.full data (n0 + 1 ) (tri_prefix_z_130 ((n0 + 1 ))) )
) \/
(
forall (n0: Z) (size: Z) (out: Z) (data: Z) (PreH1 : (n0 = 0)) (PreH2 : (size = (n0 + 1 ))) (PreH3 : (0 <= n0)) (PreH4 : (n0 <= 1000)) (PreH5 : (problem_130_pre_z n0 )) (PreH6 : (tri_safe_z_130 n0 )) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) ,
  (IntArray.seg data 0 1 (tri_prefix_z_130 (1)) )
|--
  “ (problem_130_spec_z n0 (tri_prefix_z_130 ((n0 + 1 ))) ) ”
  &&  (IntArray.full data (n0 + 1 ) (tri_prefix_z_130 ((n0 + 1 ))) )
).

Definition tri_entail_wit_2_split_goal_1 := 
forall (n0: Z) (size: Z) (out: Z) (data: Z) (PreH1 : (n0 = 0)) (PreH2 : (size = (n0 + 1 ))) (PreH3 : (0 <= n0)) (PreH4 : (n0 <= 1000)) (PreH5 : (problem_130_pre_z n0 )) (PreH6 : (tri_safe_z_130 n0 )) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) ,
  (IntArray.seg data 0 1 (tri_prefix_z_130 (1)) )
|--
  “ (problem_130_spec_z n0 (tri_prefix_z_130 ((n0 + 1 ))) ) ”
.

Definition tri_entail_wit_2_split_goal_spatial := 
forall (n0: Z) (size: Z) (out: Z) (data: Z) (PreH1 : (n0 = 0)) (PreH2 : (size = (n0 + 1 ))) (PreH3 : (0 <= n0)) (PreH4 : (n0 <= 1000)) (PreH5 : (problem_130_pre_z n0 )) (PreH6 : (tri_safe_z_130 n0 )) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) ,
  (IntArray.seg data 0 1 (tri_prefix_z_130 (1)) )
|--
  (IntArray.full data (n0 + 1 ) (tri_prefix_z_130 ((n0 + 1 ))) )
.

Definition tri_entail_wit_3 := 
(
forall (n0: Z) (size: Z) (out: Z) (data: Z) (PreH1 : (n0 <> 0)) (PreH2 : (size = (n0 + 1 ))) (PreH3 : (0 <= n0)) (PreH4 : (n0 <= 1000)) (PreH5 : (problem_130_pre_z n0 )) (PreH6 : (tri_safe_z_130 n0 )) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) ,
  (IntArray.seg data 0 (1 + 1 ) (app ((tri_prefix_z_130 (1))) ((cons (3) ((@nil Z))))) )
  **  (IntArray.undef_seg data (1 + 1 ) size )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> size)
|--
  “ (size = (n0 + 1 )) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_130_pre_z n0 ) ” 
  &&  “ (tri_safe_z_130 n0 ) ” 
  &&  “ (2 <= 2) ” 
  &&  “ (2 <= (n0 + 1 )) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> size)
  **  (IntArray.seg data 0 2 (tri_prefix_z_130 (2)) )
  **  (IntArray.undef_seg data 2 size )
) \/
(
forall (n0: Z) (size: Z) (out: Z) (data: Z) (PreH1 : (n0 <> 0)) (PreH2 : (size = (n0 + 1 ))) (PreH3 : (0 <= n0)) (PreH4 : (n0 <= 1000)) (PreH5 : (problem_130_pre_z n0 )) (PreH6 : (tri_safe_z_130 n0 )) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) ,
  (IntArray.seg data 0 (1 + 1 ) (app ((tri_prefix_z_130 (1))) ((cons (3) ((@nil Z))))) )
|--
  (IntArray.seg data 0 2 (tri_prefix_z_130 (2)) )
).

Definition tri_entail_wit_3_split_goal_spatial := 
forall (n0: Z) (size: Z) (out: Z) (data: Z) (PreH1 : (n0 <> 0)) (PreH2 : (size = (n0 + 1 ))) (PreH3 : (0 <= n0)) (PreH4 : (n0 <= 1000)) (PreH5 : (problem_130_pre_z n0 )) (PreH6 : (tri_safe_z_130 n0 )) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) ,
  (IntArray.seg data 0 (1 + 1 ) (app ((tri_prefix_z_130 (1))) ((cons (3) ((@nil Z))))) )
|--
  (IntArray.seg data 0 2 (tri_prefix_z_130 (2)) )
.

Definition tri_entail_wit_4_1 := 
(
forall (n0: Z) (data: Z) (out: Z) (i: Z) (size: Z) (PreH1 : ((i % ( 2 ) ) <> 0)) (PreH2 : (i <= n0)) (PreH3 : (size = (n0 + 1 ))) (PreH4 : (1 <= n0)) (PreH5 : (n0 <= 1000)) (PreH6 : (problem_130_pre_z n0 )) (PreH7 : (tri_safe_z_130 n0 )) (PreH8 : (2 <= i)) (PreH9 : (i <= (n0 + 1 ))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) ,
  (IntArray.seg data 0 (i + 1 ) (app ((tri_prefix_z_130 (i))) ((cons (((((Znth ((i - 1 ) - 0 ) (tri_prefix_z_130 (i)) 0) + (Znth ((i - 2 ) - 0 ) (tri_prefix_z_130 (i)) 0) ) + 1 ) + ((i + 1 ) ÷ 2 ) )) ((@nil Z))))) )
  **  (IntArray.undef_seg data (i + 1 ) size )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> size)
|--
  “ (size = (n0 + 1 )) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_130_pre_z n0 ) ” 
  &&  “ (tri_safe_z_130 n0 ) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> size)
  **  (IntArray.seg data 0 (i + 1 ) (tri_prefix_z_130 ((i + 1 ))) )
  **  (IntArray.undef_seg data (i + 1 ) size )
) \/
(
forall (n0: Z) (data: Z) (out: Z) (i: Z) (size: Z) (PreH1 : ((i % ( 2 ) ) <> 0)) (PreH2 : (i <= n0)) (PreH3 : (size = (n0 + 1 ))) (PreH4 : (1 <= n0)) (PreH5 : (n0 <= 1000)) (PreH6 : (problem_130_pre_z n0 )) (PreH7 : (tri_safe_z_130 n0 )) (PreH8 : (2 <= i)) (PreH9 : (i <= (n0 + 1 ))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) ,
  TT && emp 
|--
  “ ((app ((tri_prefix_z_130 (i))) ((cons (((((Znth ((i - 1 ) - 0 ) (tri_prefix_z_130 (i)) 0) + (Znth ((i - 2 ) - 0 ) (tri_prefix_z_130 (i)) 0) ) + 1 ) + ((i + 1 ) ÷ 2 ) )) ((@nil Z))))) = (tri_prefix_z_130 ((i + 1 )))) ”
  &&  emp
).

Definition tri_entail_wit_4_1_split_goal_1 := 
forall (n0: Z) (data: Z) (out: Z) (i: Z) (size: Z) (PreH1 : ((i % ( 2 ) ) <> 0)) (PreH2 : (i <= n0)) (PreH3 : (size = (n0 + 1 ))) (PreH4 : (1 <= n0)) (PreH5 : (n0 <= 1000)) (PreH6 : (problem_130_pre_z n0 )) (PreH7 : (tri_safe_z_130 n0 )) (PreH8 : (2 <= i)) (PreH9 : (i <= (n0 + 1 ))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) ,
  TT && emp 
|--
  “ ((app ((tri_prefix_z_130 (i))) ((cons (((((Znth ((i - 1 ) - 0 ) (tri_prefix_z_130 (i)) 0) + (Znth ((i - 2 ) - 0 ) (tri_prefix_z_130 (i)) 0) ) + 1 ) + ((i + 1 ) ÷ 2 ) )) ((@nil Z))))) = (tri_prefix_z_130 ((i + 1 )))) ”
.

Definition tri_entail_wit_4_2 := 
(
forall (n0: Z) (data: Z) (out: Z) (i: Z) (size: Z) (PreH1 : ((i % ( 2 ) ) = 0)) (PreH2 : (i <= n0)) (PreH3 : (size = (n0 + 1 ))) (PreH4 : (1 <= n0)) (PreH5 : (n0 <= 1000)) (PreH6 : (problem_130_pre_z n0 )) (PreH7 : (tri_safe_z_130 n0 )) (PreH8 : (2 <= i)) (PreH9 : (i <= (n0 + 1 ))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) ,
  (IntArray.seg data 0 (i + 1 ) (app ((tri_prefix_z_130 (i))) ((cons ((1 + (i ÷ 2 ) )) ((@nil Z))))) )
  **  (IntArray.undef_seg data (i + 1 ) size )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> size)
|--
  “ (size = (n0 + 1 )) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_130_pre_z n0 ) ” 
  &&  “ (tri_safe_z_130 n0 ) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> size)
  **  (IntArray.seg data 0 (i + 1 ) (tri_prefix_z_130 ((i + 1 ))) )
  **  (IntArray.undef_seg data (i + 1 ) size )
) \/
(
forall (n0: Z) (data: Z) (out: Z) (i: Z) (size: Z) (PreH1 : ((i % ( 2 ) ) = 0)) (PreH2 : (i <= n0)) (PreH3 : (size = (n0 + 1 ))) (PreH4 : (1 <= n0)) (PreH5 : (n0 <= 1000)) (PreH6 : (problem_130_pre_z n0 )) (PreH7 : (tri_safe_z_130 n0 )) (PreH8 : (2 <= i)) (PreH9 : (i <= (n0 + 1 ))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) ,
  TT && emp 
|--
  “ ((app ((tri_prefix_z_130 (i))) ((cons ((1 + (i ÷ 2 ) )) ((@nil Z))))) = (tri_prefix_z_130 ((i + 1 )))) ”
  &&  emp
).

Definition tri_entail_wit_4_2_split_goal_1 := 
forall (n0: Z) (data: Z) (out: Z) (i: Z) (size: Z) (PreH1 : ((i % ( 2 ) ) = 0)) (PreH2 : (i <= n0)) (PreH3 : (size = (n0 + 1 ))) (PreH4 : (1 <= n0)) (PreH5 : (n0 <= 1000)) (PreH6 : (problem_130_pre_z n0 )) (PreH7 : (tri_safe_z_130 n0 )) (PreH8 : (2 <= i)) (PreH9 : (i <= (n0 + 1 ))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) ,
  TT && emp 
|--
  “ ((app ((tri_prefix_z_130 (i))) ((cons ((1 + (i ÷ 2 ) )) ((@nil Z))))) = (tri_prefix_z_130 ((i + 1 )))) ”
.

Definition tri_entail_wit_5 := 
forall (n0: Z) (size: Z) (i: Z) (out: Z) (data: Z) (PreH1 : (size = (n0 + 1 ))) (PreH2 : (1 <= n0)) (PreH3 : (n0 <= 1000)) (PreH4 : (problem_130_pre_z n0 )) (PreH5 : (tri_safe_z_130 n0 )) (PreH6 : (2 <= i)) (PreH7 : (i <= n0)) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> size)
  **  (IntArray.seg data 0 (i + 1 ) (tri_prefix_z_130 ((i + 1 ))) )
  **  (IntArray.undef_seg data (i + 1 ) size )
|--
  “ (size = (n0 + 1 )) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_130_pre_z n0 ) ” 
  &&  “ (tri_safe_z_130 n0 ) ” 
  &&  “ (2 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (n0 + 1 )) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> size)
  **  (IntArray.seg data 0 (i + 1 ) (tri_prefix_z_130 ((i + 1 ))) )
  **  (IntArray.undef_seg data (i + 1 ) size )
.

Definition tri_entail_wit_6 := 
(
forall (n0: Z) (data: Z) (out: Z) (i: Z) (size: Z) (PreH1 : (i > n0)) (PreH2 : (size = (n0 + 1 ))) (PreH3 : (1 <= n0)) (PreH4 : (n0 <= 1000)) (PreH5 : (problem_130_pre_z n0 )) (PreH6 : (tri_safe_z_130 n0 )) (PreH7 : (2 <= i)) (PreH8 : (i <= (n0 + 1 ))) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> size)
  **  (IntArray.seg data 0 i (tri_prefix_z_130 (i)) )
  **  (IntArray.undef_seg data i size )
|--
  “ (size = (n0 + 1 )) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_130_pre_z n0 ) ” 
  &&  “ (tri_safe_z_130 n0 ) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (problem_130_spec_z n0 (tri_prefix_z_130 ((n0 + 1 ))) ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (n0 + 1 ))
  **  (IntArray.full data (n0 + 1 ) (tri_prefix_z_130 ((n0 + 1 ))) )
) \/
(
forall (n0: Z) (data: Z) (out: Z) (i: Z) (size: Z) (PreH1 : (i > n0)) (PreH2 : (size = (n0 + 1 ))) (PreH3 : (1 <= n0)) (PreH4 : (n0 <= 1000)) (PreH5 : (problem_130_pre_z n0 )) (PreH6 : (tri_safe_z_130 n0 )) (PreH7 : (2 <= i)) (PreH8 : (i <= (n0 + 1 ))) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) ,
  (IntArray.seg data 0 i (tri_prefix_z_130 (i)) )
|--
  “ (problem_130_spec_z n0 (tri_prefix_z_130 ((n0 + 1 ))) ) ”
  &&  (IntArray.full data (n0 + 1 ) (tri_prefix_z_130 ((n0 + 1 ))) )
).

Definition tri_entail_wit_6_split_goal_1 := 
forall (n0: Z) (data: Z) (out: Z) (i: Z) (size: Z) (PreH1 : (i > n0)) (PreH2 : (size = (n0 + 1 ))) (PreH3 : (1 <= n0)) (PreH4 : (n0 <= 1000)) (PreH5 : (problem_130_pre_z n0 )) (PreH6 : (tri_safe_z_130 n0 )) (PreH7 : (2 <= i)) (PreH8 : (i <= (n0 + 1 ))) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) ,
  (IntArray.seg data 0 i (tri_prefix_z_130 (i)) )
|--
  “ (problem_130_spec_z n0 (tri_prefix_z_130 ((n0 + 1 ))) ) ”
.

Definition tri_entail_wit_6_split_goal_spatial := 
forall (n0: Z) (data: Z) (out: Z) (i: Z) (size: Z) (PreH1 : (i > n0)) (PreH2 : (size = (n0 + 1 ))) (PreH3 : (1 <= n0)) (PreH4 : (n0 <= 1000)) (PreH5 : (problem_130_pre_z n0 )) (PreH6 : (tri_safe_z_130 n0 )) (PreH7 : (2 <= i)) (PreH8 : (i <= (n0 + 1 ))) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) ,
  (IntArray.seg data 0 i (tri_prefix_z_130 (i)) )
|--
  (IntArray.full data (n0 + 1 ) (tri_prefix_z_130 ((n0 + 1 ))) )
.

Definition tri_return_wit_1 := 
forall (n0: Z) (size: Z) (out: Z) (data_2: Z) (PreH1 : (size = (n0 + 1 ))) (PreH2 : (1 <= n0)) (PreH3 : (n0 <= 1000)) (PreH4 : (problem_130_pre_z n0 )) (PreH5 : (tri_safe_z_130 n0 )) (PreH6 : (out <> 0)) (PreH7 : (data_2 <> 0)) (PreH8 : (problem_130_spec_z n0 (tri_prefix_z_130 ((n0 + 1 ))) )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data_2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (n0 + 1 ))
  **  (IntArray.full data_2 (n0 + 1 ) (tri_prefix_z_130 ((n0 + 1 ))) )
|--
  EX (data: Z) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (problem_130_spec_z n0 (tri_prefix_z_130 ((n0 + 1 ))) ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (n0 + 1 ))
  **  (IntArray.full data (n0 + 1 ) (tri_prefix_z_130 ((n0 + 1 ))) )
.

Definition tri_return_wit_2 := 
forall (n0: Z) (size: Z) (out: Z) (data_2: Z) (PreH1 : (n0 = 0)) (PreH2 : (size = (n0 + 1 ))) (PreH3 : (problem_130_pre_z n0 )) (PreH4 : (tri_safe_z_130 n0 )) (PreH5 : (out <> 0)) (PreH6 : (data_2 <> 0)) (PreH7 : (problem_130_spec_z n0 (tri_prefix_z_130 ((n0 + 1 ))) )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data_2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (n0 + 1 ))
  **  (IntArray.full data_2 (n0 + 1 ) (tri_prefix_z_130 ((n0 + 1 ))) )
|--
  EX (data: Z) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (problem_130_spec_z n0 (tri_prefix_z_130 ((n0 + 1 ))) ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (n0 + 1 ))
  **  (IntArray.full data (n0 + 1 ) (tri_prefix_z_130 ((n0 + 1 ))) )
.

Definition tri_partial_solve_wit_1 := 
forall (n_pre: Z) (n0: Z) (PreH1 : (n_pre = n0)) (PreH2 : (0 <= n0)) (PreH3 : (n0 <= 1000)) (PreH4 : (problem_130_pre_z n0 )) (PreH5 : (tri_safe_z_130 n0 )) ,
  TT && emp 
|--
  “ (n_pre = n0) ” 
  &&  “ (0 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_130_pre_z n0 ) ” 
  &&  “ (tri_safe_z_130 n0 ) ”
  &&  emp
.

Definition tri_partial_solve_wit_2_pure := 
forall (n_pre: Z) (n0: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (n_pre = n0)) (PreH3 : (0 <= n0)) (PreH4 : (n0 <= 1000)) (PreH5 : (problem_130_pre_z n0 )) (PreH6 : (tri_safe_z_130 n0 )) ,
  ((( &( "data" ) )) # Ptr  |->_)
  **  ((( &( "size" ) )) # Int  |-> (n_pre + 1 ))
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((n_pre + 1 ) > 0) ” 
  &&  “ ((n_pre + 1 ) < INT_MAX) ”
.

Definition tri_partial_solve_wit_2_aux := 
forall (n_pre: Z) (n0: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (n_pre = n0)) (PreH3 : (0 <= n0)) (PreH4 : (n0 <= 1000)) (PreH5 : (problem_130_pre_z n0 )) (PreH6 : (tri_safe_z_130 n0 )) ,
  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  “ ((n_pre + 1 ) > 0) ” 
  &&  “ ((n_pre + 1 ) < INT_MAX) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (n_pre = n0) ” 
  &&  “ (0 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_130_pre_z n0 ) ” 
  &&  “ (tri_safe_z_130 n0 ) ”
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
.

Definition tri_partial_solve_wit_2 := tri_partial_solve_wit_2_pure -> tri_partial_solve_wit_2_aux.

Definition tri_partial_solve_wit_3 := 
forall (n_pre: Z) (n0: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (n_pre = n0)) (PreH4 : (0 <= n0)) (PreH5 : (n0 <= 1000)) (PreH6 : (problem_130_pre_z n0 )) (PreH7 : (tri_safe_z_130 n0 )) ,
  (IntArray.undef_full retval_2 (n_pre + 1 ) )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (n_pre + 1 ))
|--
  “ (retval_2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (n_pre = n0) ” 
  &&  “ (0 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_130_pre_z n0 ) ” 
  &&  “ (tri_safe_z_130 n0 ) ”
  &&  (((retval_2 + (0 * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg retval_2 1 (n_pre + 1 ) )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (n_pre + 1 ))
.

Definition tri_partial_solve_wit_4 := 
forall (n0: Z) (size: Z) (out: Z) (data: Z) (PreH1 : (n0 <> 0)) (PreH2 : (size = (n0 + 1 ))) (PreH3 : (0 <= n0)) (PreH4 : (n0 <= 1000)) (PreH5 : (problem_130_pre_z n0 )) (PreH6 : (tri_safe_z_130 n0 )) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> size)
  **  (IntArray.seg data 0 1 (tri_prefix_z_130 (1)) )
  **  (IntArray.undef_seg data 1 size )
|--
  “ (n0 <> 0) ” 
  &&  “ (size = (n0 + 1 )) ” 
  &&  “ (0 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_130_pre_z n0 ) ” 
  &&  “ (tri_safe_z_130 n0 ) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ”
  &&  (((data + (1 * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg data (1 + 1 ) size )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> size)
  **  (IntArray.seg data 0 1 (tri_prefix_z_130 (1)) )
.

Definition tri_partial_solve_wit_5 := 
forall (n0: Z) (data: Z) (out: Z) (i: Z) (size: Z) (PreH1 : ((i % ( 2 ) ) = 0)) (PreH2 : (i <= n0)) (PreH3 : (size = (n0 + 1 ))) (PreH4 : (1 <= n0)) (PreH5 : (n0 <= 1000)) (PreH6 : (problem_130_pre_z n0 )) (PreH7 : (tri_safe_z_130 n0 )) (PreH8 : (2 <= i)) (PreH9 : (i <= (n0 + 1 ))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> size)
  **  (IntArray.seg data 0 i (tri_prefix_z_130 (i)) )
  **  (IntArray.undef_seg data i size )
|--
  “ ((i % ( 2 ) ) = 0) ” 
  &&  “ (i <= n0) ” 
  &&  “ (size = (n0 + 1 )) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_130_pre_z n0 ) ” 
  &&  “ (tri_safe_z_130 n0 ) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ”
  &&  (((data + (i * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg data (i + 1 ) size )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> size)
  **  (IntArray.seg data 0 i (tri_prefix_z_130 (i)) )
.

Definition tri_partial_solve_wit_6 := 
forall (n0: Z) (data: Z) (out: Z) (i: Z) (size: Z) (PreH1 : ((i % ( 2 ) ) <> 0)) (PreH2 : (i <= n0)) (PreH3 : (size = (n0 + 1 ))) (PreH4 : (1 <= n0)) (PreH5 : (n0 <= 1000)) (PreH6 : (problem_130_pre_z n0 )) (PreH7 : (tri_safe_z_130 n0 )) (PreH8 : (2 <= i)) (PreH9 : (i <= (n0 + 1 ))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> size)
  **  (IntArray.seg data 0 i (tri_prefix_z_130 (i)) )
  **  (IntArray.undef_seg data i size )
|--
  “ ((i % ( 2 ) ) <> 0) ” 
  &&  “ (i <= n0) ” 
  &&  “ (size = (n0 + 1 )) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_130_pre_z n0 ) ” 
  &&  “ (tri_safe_z_130 n0 ) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ”
  &&  (((data + ((i - 1 ) * sizeof(INT) ) )) # Int  |-> (Znth ((i - 1 ) - 0 ) (tri_prefix_z_130 (i)) 0))
  **  (IntArray.missing_i data (i - 1 ) 0 i (tri_prefix_z_130 (i)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> size)
  **  (IntArray.undef_seg data i size )
.

Definition tri_partial_solve_wit_7 := 
forall (n0: Z) (data: Z) (out: Z) (i: Z) (size: Z) (PreH1 : ((i % ( 2 ) ) <> 0)) (PreH2 : (i <= n0)) (PreH3 : (size = (n0 + 1 ))) (PreH4 : (1 <= n0)) (PreH5 : (n0 <= 1000)) (PreH6 : (problem_130_pre_z n0 )) (PreH7 : (tri_safe_z_130 n0 )) (PreH8 : (2 <= i)) (PreH9 : (i <= (n0 + 1 ))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) ,
  (IntArray.seg data 0 i (tri_prefix_z_130 (i)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> size)
  **  (IntArray.undef_seg data i size )
|--
  “ ((i % ( 2 ) ) <> 0) ” 
  &&  “ (i <= n0) ” 
  &&  “ (size = (n0 + 1 )) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_130_pre_z n0 ) ” 
  &&  “ (tri_safe_z_130 n0 ) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ”
  &&  (((data + ((i - 2 ) * sizeof(INT) ) )) # Int  |-> (Znth ((i - 2 ) - 0 ) (tri_prefix_z_130 (i)) 0))
  **  (IntArray.missing_i data (i - 2 ) 0 i (tri_prefix_z_130 (i)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> size)
  **  (IntArray.undef_seg data i size )
.

Definition tri_partial_solve_wit_8 := 
forall (n0: Z) (data: Z) (out: Z) (i: Z) (size: Z) (PreH1 : ((i % ( 2 ) ) <> 0)) (PreH2 : (i <= n0)) (PreH3 : (size = (n0 + 1 ))) (PreH4 : (1 <= n0)) (PreH5 : (n0 <= 1000)) (PreH6 : (problem_130_pre_z n0 )) (PreH7 : (tri_safe_z_130 n0 )) (PreH8 : (2 <= i)) (PreH9 : (i <= (n0 + 1 ))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) ,
  (IntArray.seg data 0 i (tri_prefix_z_130 (i)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> size)
  **  (IntArray.undef_seg data i size )
|--
  “ ((i % ( 2 ) ) <> 0) ” 
  &&  “ (i <= n0) ” 
  &&  “ (size = (n0 + 1 )) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_130_pre_z n0 ) ” 
  &&  “ (tri_safe_z_130 n0 ) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ”
  &&  (((data + (i * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg data (i + 1 ) size )
  **  (IntArray.seg data 0 i (tri_prefix_z_130 (i)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> size)
.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_tri_safety_wit_1 : tri_safety_wit_1.
Axiom proof_of_tri_safety_wit_2 : tri_safety_wit_2.
Axiom proof_of_tri_safety_wit_3 : tri_safety_wit_3.
Axiom proof_of_tri_safety_wit_4 : tri_safety_wit_4.
Axiom proof_of_tri_safety_wit_5 : tri_safety_wit_5.
Axiom proof_of_tri_safety_wit_6 : tri_safety_wit_6.
Axiom proof_of_tri_safety_wit_7 : tri_safety_wit_7.
Axiom proof_of_tri_safety_wit_8 : tri_safety_wit_8.
Axiom proof_of_tri_safety_wit_9 : tri_safety_wit_9.
Axiom proof_of_tri_safety_wit_10 : tri_safety_wit_10.
Axiom proof_of_tri_safety_wit_11 : tri_safety_wit_11.
Axiom proof_of_tri_safety_wit_12 : tri_safety_wit_12.
Axiom proof_of_tri_safety_wit_13 : tri_safety_wit_13.
Axiom proof_of_tri_safety_wit_14 : tri_safety_wit_14.
Axiom proof_of_tri_safety_wit_15 : tri_safety_wit_15.
Axiom proof_of_tri_safety_wit_16 : tri_safety_wit_16.
Axiom proof_of_tri_safety_wit_17 : tri_safety_wit_17.
Axiom proof_of_tri_safety_wit_18 : tri_safety_wit_18.
Axiom proof_of_tri_safety_wit_19 : tri_safety_wit_19.
Axiom proof_of_tri_safety_wit_20 : tri_safety_wit_20.
Axiom proof_of_tri_safety_wit_21 : tri_safety_wit_21.
Axiom proof_of_tri_safety_wit_22 : tri_safety_wit_22.
Axiom proof_of_tri_safety_wit_23 : tri_safety_wit_23.
Axiom proof_of_tri_safety_wit_24 : tri_safety_wit_24.
Axiom proof_of_tri_safety_wit_25 : tri_safety_wit_25.
Axiom proof_of_tri_safety_wit_26 : tri_safety_wit_26.
Axiom proof_of_tri_safety_wit_27 : tri_safety_wit_27.
Axiom proof_of_tri_safety_wit_28 : tri_safety_wit_28.
Axiom proof_of_tri_entail_wit_1 : tri_entail_wit_1.
Axiom proof_of_tri_entail_wit_2 : tri_entail_wit_2.
Axiom proof_of_tri_entail_wit_3 : tri_entail_wit_3.
Axiom proof_of_tri_entail_wit_4_1 : tri_entail_wit_4_1.
Axiom proof_of_tri_entail_wit_4_2 : tri_entail_wit_4_2.
Axiom proof_of_tri_entail_wit_5 : tri_entail_wit_5.
Axiom proof_of_tri_entail_wit_6 : tri_entail_wit_6.
Axiom proof_of_tri_return_wit_1 : tri_return_wit_1.
Axiom proof_of_tri_return_wit_2 : tri_return_wit_2.
Axiom proof_of_tri_partial_solve_wit_1 : tri_partial_solve_wit_1.
Axiom proof_of_tri_partial_solve_wit_2_pure : tri_partial_solve_wit_2_pure.
Axiom proof_of_tri_partial_solve_wit_2 : tri_partial_solve_wit_2.
Axiom proof_of_tri_partial_solve_wit_3 : tri_partial_solve_wit_3.
Axiom proof_of_tri_partial_solve_wit_4 : tri_partial_solve_wit_4.
Axiom proof_of_tri_partial_solve_wit_5 : tri_partial_solve_wit_5.
Axiom proof_of_tri_partial_solve_wit_6 : tri_partial_solve_wit_6.
Axiom proof_of_tri_partial_solve_wit_7 : tri_partial_solve_wit_7.
Axiom proof_of_tri_partial_solve_wit_8 : tri_partial_solve_wit_8.

End VC_Correct.
