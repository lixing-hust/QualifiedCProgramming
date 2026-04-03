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

(*----- Function make_a_pile -----*)

Definition make_a_pile_safety_wit_1 := 
forall (out_pre: Z) (n_pre: Z) ,
  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.undef_full out_pre n_pre )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition make_a_pile_safety_wit_2 := 
forall (out_pre: Z) (n_pre: Z) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.seg out_pre 0 i (sublist (0) (i) ((make_pile (n_pre)))) )
  **  (IntArray.undef_seg out_pre i n_pre )
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| ((n_pre + (2 * i ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (n_pre + (2 * i ) )) |]
.

Definition make_a_pile_safety_wit_3 := 
forall (out_pre: Z) (n_pre: Z) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.seg out_pre 0 i (sublist (0) (i) ((make_pile (n_pre)))) )
  **  (IntArray.undef_seg out_pre i n_pre )
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| ((2 * i ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (2 * i )) |]
.

Definition make_a_pile_safety_wit_4 := 
forall (out_pre: Z) (n_pre: Z) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.seg out_pre 0 i (sublist (0) (i) ((make_pile (n_pre)))) )
  **  (IntArray.undef_seg out_pre i n_pre )
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition make_a_pile_safety_wit_5 := 
forall (out_pre: Z) (n_pre: Z) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  (((out_pre + (i * sizeof(INT) ) )) # Int  |-> (n_pre + (2 * i ) ))
  **  (IntArray.undef_seg out_pre (i + 1 ) n_pre )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.seg out_pre 0 i (sublist (0) (i) ((make_pile (n_pre)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition make_a_pile_entail_wit_1 := 
forall (out_pre: Z) (n_pre: Z) ,
  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  (IntArray.undef_full out_pre n_pre )
|--
  [| (0 <= 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  (IntArray.seg out_pre 0 0 (sublist (0) (0) ((make_pile (n_pre)))) )
  **  (IntArray.undef_seg out_pre 0 n_pre )
.

Definition make_a_pile_entail_wit_2 := 
forall (out_pre: Z) (n_pre: Z) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  (((out_pre + (i * sizeof(INT) ) )) # Int  |-> (n_pre + (2 * i ) ))
  **  (IntArray.undef_seg out_pre (i + 1 ) n_pre )
  **  (IntArray.seg out_pre 0 i (sublist (0) (i) ((make_pile (n_pre)))) )
|--
  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n_pre) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  (IntArray.seg out_pre 0 (i + 1 ) (sublist (0) ((i + 1 )) ((make_pile (n_pre)))) )
  **  (IntArray.undef_seg out_pre (i + 1 ) n_pre )
.

Definition make_a_pile_return_wit_1 := 
forall (out_pre: Z) (n_pre: Z) (i: Z) ,
  [| (i >= n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  (IntArray.seg out_pre 0 i (sublist (0) (i) ((make_pile (n_pre)))) )
  **  (IntArray.undef_seg out_pre i n_pre )
|--
  (IntArray.full out_pre n_pre (make_pile (n_pre)) )
.

Definition make_a_pile_partial_solve_wit_1 := 
forall (out_pre: Z) (n_pre: Z) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  (IntArray.seg out_pre 0 i (sublist (0) (i) ((make_pile (n_pre)))) )
  **  (IntArray.undef_seg out_pre i n_pre )
|--
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  (((out_pre + (i * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg out_pre (i + 1 ) n_pre )
  **  (IntArray.seg out_pre 0 i (sublist (0) (i) ((make_pile (n_pre)))) )
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_make_a_pile_safety_wit_1 : make_a_pile_safety_wit_1.
Axiom proof_of_make_a_pile_safety_wit_2 : make_a_pile_safety_wit_2.
Axiom proof_of_make_a_pile_safety_wit_3 : make_a_pile_safety_wit_3.
Axiom proof_of_make_a_pile_safety_wit_4 : make_a_pile_safety_wit_4.
Axiom proof_of_make_a_pile_safety_wit_5 : make_a_pile_safety_wit_5.
Axiom proof_of_make_a_pile_entail_wit_1 : make_a_pile_entail_wit_1.
Axiom proof_of_make_a_pile_entail_wit_2 : make_a_pile_entail_wit_2.
Axiom proof_of_make_a_pile_return_wit_1 : make_a_pile_return_wit_1.
Axiom proof_of_make_a_pile_partial_solve_wit_1 : make_a_pile_partial_solve_wit_1.

End VC_Correct.
