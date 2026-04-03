Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.
From SimpleC.EE Require Import common_strategy_goal.
From SimpleC.EE Require Import common_strategy_proof.
From SimpleC.EE Require Import int_array_strategy_goal.
From SimpleC.EE Require Import int_array_strategy_proof.
From SimpleC.EE Require Import uint_array_strategy_goal.
From SimpleC.EE Require Import uint_array_strategy_proof.
From SimpleC.EE Require Import undef_uint_array_strategy_goal.
From SimpleC.EE Require Import undef_uint_array_strategy_proof.
From SimpleC.EE Require Import array_shape_strategy_goal.
From SimpleC.EE Require Import array_shape_strategy_proof.

(*----- Function incr_list -----*)

Definition incr_list_safety_wit_1 := 
forall (out_pre: Z) (l_size_pre: Z) (l_pre: Z) (lv: (@list Z)) ,
  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < INT_MAX) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  (IntArray.full l_pre l_size_pre lv )
  **  (IntArray.undef_full out_pre l_size_pre )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition incr_list_safety_wit_2 := 
forall (out_pre: Z) (l_size_pre: Z) (lv: (@list Z)) (l: Z) (i: Z) ,
  [| (i < l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l_size_pre) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < INT_MAX) |]
  &&  (IntArray.full l l_size_pre lv )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "l" ) )) # Ptr  |-> l)
  **  (IntArray.seg out_pre 0 i (map_incr ((sublist (0) (i) (lv)))) )
  **  (IntArray.undef_seg out_pre i l_size_pre )
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
|--
  [| (((Znth i lv 0) + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((Znth i lv 0) + 1 )) |]
.

Definition incr_list_safety_wit_3 := 
forall (out_pre: Z) (l_size_pre: Z) (lv: (@list Z)) (l: Z) (i: Z) ,
  [| (i < l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l_size_pre) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < INT_MAX) |]
  &&  (IntArray.full l l_size_pre lv )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "l" ) )) # Ptr  |-> l)
  **  (IntArray.seg out_pre 0 i (map_incr ((sublist (0) (i) (lv)))) )
  **  (IntArray.undef_seg out_pre i l_size_pre )
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition incr_list_safety_wit_4 := 
forall (out_pre: Z) (l_size_pre: Z) (lv: (@list Z)) (l: Z) (i: Z) ,
  [| (i < l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l_size_pre) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < INT_MAX) |]
  &&  (((out_pre + (i * sizeof(INT) ) )) # Int  |-> ((Znth i lv 0) + 1 ))
  **  (IntArray.undef_seg out_pre (i + 1 ) l_size_pre )
  **  (IntArray.full l l_size_pre lv )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "l" ) )) # Ptr  |-> l)
  **  (IntArray.seg out_pre 0 i (map_incr ((sublist (0) (i) (lv)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition incr_list_entail_wit_1 := 
forall (out_pre: Z) (l_size_pre: Z) (l_pre: Z) (lv: (@list Z)) ,
  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < INT_MAX) |]
  &&  (IntArray.full l_pre l_size_pre lv )
  **  (IntArray.undef_full out_pre l_size_pre )
|--
  [| (0 <= 0) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < INT_MAX) |]
  &&  (IntArray.full l_pre l_size_pre lv )
  **  (IntArray.seg out_pre 0 0 (map_incr ((sublist (0) (0) (lv)))) )
  **  (IntArray.undef_seg out_pre 0 l_size_pre )
.

Definition incr_list_entail_wit_2 := 
forall (out_pre: Z) (l_size_pre: Z) (lv: (@list Z)) (l: Z) (i: Z) ,
  [| (i < l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l_size_pre) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < INT_MAX) |]
  &&  (((out_pre + (i * sizeof(INT) ) )) # Int  |-> ((Znth i lv 0) + 1 ))
  **  (IntArray.undef_seg out_pre (i + 1 ) l_size_pre )
  **  (IntArray.full l l_size_pre lv )
  **  (IntArray.seg out_pre 0 i (map_incr ((sublist (0) (i) (lv)))) )
|--
  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= l_size_pre) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < INT_MAX) |]
  &&  (IntArray.full l l_size_pre lv )
  **  (IntArray.seg out_pre 0 (i + 1 ) (map_incr ((sublist (0) ((i + 1 )) (lv)))) )
  **  (IntArray.undef_seg out_pre (i + 1 ) l_size_pre )
.

Definition incr_list_return_wit_1 := 
forall (out_pre: Z) (l_size_pre: Z) (l_pre: Z) (lv: (@list Z)) (l: Z) (i: Z) ,
  [| (i >= l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l_size_pre) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < INT_MAX) |]
  &&  (IntArray.full l l_size_pre lv )
  **  (IntArray.seg out_pre 0 i (map_incr ((sublist (0) (i) (lv)))) )
  **  (IntArray.undef_seg out_pre i l_size_pre )
|--
  (IntArray.full l_pre l_size_pre lv )
  **  (IntArray.full out_pre l_size_pre (map_incr (lv)) )
.

Definition incr_list_partial_solve_wit_1 := 
forall (out_pre: Z) (l_size_pre: Z) (lv: (@list Z)) (l: Z) (i: Z) ,
  [| (i < l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l_size_pre) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < INT_MAX) |]
  &&  (IntArray.full l l_size_pre lv )
  **  (IntArray.seg out_pre 0 i (map_incr ((sublist (0) (i) (lv)))) )
  **  (IntArray.undef_seg out_pre i l_size_pre )
|--
  [| (i < l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l_size_pre) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < INT_MAX) |]
  &&  (((l + (i * sizeof(INT) ) )) # Int  |-> (Znth i lv 0))
  **  (IntArray.missing_i l i 0 l_size_pre lv )
  **  (IntArray.seg out_pre 0 i (map_incr ((sublist (0) (i) (lv)))) )
  **  (IntArray.undef_seg out_pre i l_size_pre )
.

Definition incr_list_partial_solve_wit_2 := 
forall (out_pre: Z) (l_size_pre: Z) (lv: (@list Z)) (l: Z) (i: Z) ,
  [| (i < l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l_size_pre) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < INT_MAX) |]
  &&  (IntArray.full l l_size_pre lv )
  **  (IntArray.seg out_pre 0 i (map_incr ((sublist (0) (i) (lv)))) )
  **  (IntArray.undef_seg out_pre i l_size_pre )
|--
  [| (i < l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l_size_pre) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < INT_MAX) |]
  &&  (((out_pre + (i * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg out_pre (i + 1 ) l_size_pre )
  **  (IntArray.full l l_size_pre lv )
  **  (IntArray.seg out_pre 0 i (map_incr ((sublist (0) (i) (lv)))) )
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_incr_list_safety_wit_1 : incr_list_safety_wit_1.
Axiom proof_of_incr_list_safety_wit_2 : incr_list_safety_wit_2.
Axiom proof_of_incr_list_safety_wit_3 : incr_list_safety_wit_3.
Axiom proof_of_incr_list_safety_wit_4 : incr_list_safety_wit_4.
Axiom proof_of_incr_list_entail_wit_1 : incr_list_entail_wit_1.
Axiom proof_of_incr_list_entail_wit_2 : incr_list_entail_wit_2.
Axiom proof_of_incr_list_return_wit_1 : incr_list_return_wit_1.
Axiom proof_of_incr_list_partial_solve_wit_1 : incr_list_partial_solve_wit_1.
Axiom proof_of_incr_list_partial_solve_wit_2 : incr_list_partial_solve_wit_2.

End VC_Correct.
