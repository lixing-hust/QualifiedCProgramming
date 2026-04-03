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

(*----- Function f -----*)

Definition f_safety_wit_1 := 
forall (out_pre: Z) (n_pre: Z) ,
  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  ((( &( "s" ) )) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.undef_full out_pre n_pre )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition f_safety_wit_2 := 
forall (out_pre: Z) (n_pre: Z) ,
  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  ((( &( "p" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.undef_full out_pre n_pre )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition f_safety_wit_3 := 
forall (out_pre: Z) (n_pre: Z) ,
  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "p" ) )) # Int  |-> 1)
  **  ((( &( "s" ) )) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.undef_full out_pre n_pre )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition f_safety_wit_4 := 
forall (out_pre: Z) (n_pre: Z) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.seg out_pre 0 i (sublist (0) (i) ((f_seq (n_pre)))) )
  **  (IntArray.undef_seg out_pre i n_pre )
  **  ((( &( "p" ) )) # Int  |-> 1)
  **  ((( &( "s" ) )) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| ((0 + (i + 1 ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (0 + (i + 1 ) )) |]
.

Definition f_safety_wit_5 := 
forall (out_pre: Z) (n_pre: Z) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.seg out_pre 0 i (sublist (0) (i) ((f_seq (n_pre)))) )
  **  (IntArray.undef_seg out_pre i n_pre )
  **  ((( &( "p" ) )) # Int  |-> 1)
  **  ((( &( "s" ) )) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition f_safety_wit_6 := 
forall (out_pre: Z) (n_pre: Z) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.seg out_pre 0 i (sublist (0) (i) ((f_seq (n_pre)))) )
  **  (IntArray.undef_seg out_pre i n_pre )
  **  ((( &( "p" ) )) # Int  |-> 1)
  **  ((( &( "s" ) )) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition f_safety_wit_7 := 
forall (out_pre: Z) (n_pre: Z) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.seg out_pre 0 i (sublist (0) (i) ((f_seq (n_pre)))) )
  **  (IntArray.undef_seg out_pre i n_pre )
  **  ((( &( "p" ) )) # Int  |-> 1)
  **  ((( &( "s" ) )) # Int  |-> (0 + (i + 1 ) ))
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| ((1 * (i + 1 ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (1 * (i + 1 ) )) |]
.

Definition f_safety_wit_8 := 
forall (out_pre: Z) (n_pre: Z) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.seg out_pre 0 i (sublist (0) (i) ((f_seq (n_pre)))) )
  **  (IntArray.undef_seg out_pre i n_pre )
  **  ((( &( "p" ) )) # Int  |-> 1)
  **  ((( &( "s" ) )) # Int  |-> (0 + (i + 1 ) ))
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition f_safety_wit_9 := 
forall (out_pre: Z) (n_pre: Z) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.seg out_pre 0 i (sublist (0) (i) ((f_seq (n_pre)))) )
  **  (IntArray.undef_seg out_pre i n_pre )
  **  ((( &( "p" ) )) # Int  |-> 1)
  **  ((( &( "s" ) )) # Int  |-> (0 + (i + 1 ) ))
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition f_safety_wit_10 := 
forall (out_pre: Z) (n_pre: Z) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.seg out_pre 0 i (sublist (0) (i) ((f_seq (n_pre)))) )
  **  (IntArray.undef_seg out_pre i n_pre )
  **  ((( &( "p" ) )) # Int  |-> (1 * (i + 1 ) ))
  **  ((( &( "s" ) )) # Int  |-> (0 + (i + 1 ) ))
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (((i + 1 ) <> (INT_MIN)) \/ (2 <> (-1))) |] 
  &&  [| (2 <> 0) |]
.

Definition f_safety_wit_11 := 
forall (out_pre: Z) (n_pre: Z) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.seg out_pre 0 i (sublist (0) (i) ((f_seq (n_pre)))) )
  **  (IntArray.undef_seg out_pre i n_pre )
  **  ((( &( "p" ) )) # Int  |-> (1 * (i + 1 ) ))
  **  ((( &( "s" ) )) # Int  |-> (0 + (i + 1 ) ))
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition f_safety_wit_12 := 
forall (out_pre: Z) (n_pre: Z) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.seg out_pre 0 i (sublist (0) (i) ((f_seq (n_pre)))) )
  **  (IntArray.undef_seg out_pre i n_pre )
  **  ((( &( "p" ) )) # Int  |-> (1 * (i + 1 ) ))
  **  ((( &( "s" ) )) # Int  |-> (0 + (i + 1 ) ))
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition f_safety_wit_13 := 
forall (out_pre: Z) (n_pre: Z) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.seg out_pre 0 i (sublist (0) (i) ((f_seq (n_pre)))) )
  **  (IntArray.undef_seg out_pre i n_pre )
  **  ((( &( "p" ) )) # Int  |-> (1 * (i + 1 ) ))
  **  ((( &( "s" ) )) # Int  |-> (0 + (i + 1 ) ))
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition f_safety_wit_14 := 
forall (out_pre: Z) (n_pre: Z) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.seg out_pre 0 i (sublist (0) (i) ((f_seq (n_pre)))) )
  **  (IntArray.undef_seg out_pre i n_pre )
  **  ((( &( "p" ) )) # Int  |-> (1 * (i + 1 ) ))
  **  ((( &( "s" ) )) # Int  |-> (0 + (i + 1 ) ))
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition f_safety_wit_15 := 
forall (out_pre: Z) (n_pre: Z) (i: Z) ,
  [| (((i + 1 ) % ( 2 ) ) = 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  (((out_pre + (i * sizeof(INT) ) )) # Int  |-> (1 * (i + 1 ) ))
  **  (IntArray.undef_seg out_pre (i + 1 ) n_pre )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.seg out_pre 0 i (sublist (0) (i) ((f_seq (n_pre)))) )
  **  ((( &( "p" ) )) # Int  |-> (1 * (i + 1 ) ))
  **  ((( &( "s" ) )) # Int  |-> (0 + (i + 1 ) ))
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition f_safety_wit_16 := 
forall (out_pre: Z) (n_pre: Z) (i: Z) ,
  [| (((i + 1 ) % ( 2 ) ) <> 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  (((out_pre + (i * sizeof(INT) ) )) # Int  |-> (0 + (i + 1 ) ))
  **  (IntArray.undef_seg out_pre (i + 1 ) n_pre )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.seg out_pre 0 i (sublist (0) (i) ((f_seq (n_pre)))) )
  **  ((( &( "p" ) )) # Int  |-> (1 * (i + 1 ) ))
  **  ((( &( "s" ) )) # Int  |-> (0 + (i + 1 ) ))
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition f_entail_wit_1 := 
forall (out_pre: Z) (n_pre: Z) ,
  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  (IntArray.undef_full out_pre n_pre )
|--
  [| (0 <= 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  (IntArray.seg out_pre 0 0 (sublist (0) (0) ((f_seq (n_pre)))) )
  **  (IntArray.undef_seg out_pre 0 n_pre )
.

Definition f_entail_wit_2_1 := 
forall (out_pre: Z) (n_pre: Z) (i: Z) ,
  [| (((i + 1 ) % ( 2 ) ) <> 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  (((out_pre + (i * sizeof(INT) ) )) # Int  |-> (0 + (i + 1 ) ))
  **  (IntArray.undef_seg out_pre (i + 1 ) n_pre )
  **  (IntArray.seg out_pre 0 i (sublist (0) (i) ((f_seq (n_pre)))) )
  **  ((( &( "p" ) )) # Int  |-> (1 * (i + 1 ) ))
  **  ((( &( "s" ) )) # Int  |-> (0 + (i + 1 ) ))
|--
  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n_pre) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  (IntArray.seg out_pre 0 (i + 1 ) (sublist (0) ((i + 1 )) ((f_seq (n_pre)))) )
  **  (IntArray.undef_seg out_pre (i + 1 ) n_pre )
  **  ((( &( "p" ) )) # Int  |-> 1)
  **  ((( &( "s" ) )) # Int  |-> 0)
.

Definition f_entail_wit_2_2 := 
forall (out_pre: Z) (n_pre: Z) (i: Z) ,
  [| (((i + 1 ) % ( 2 ) ) = 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  (((out_pre + (i * sizeof(INT) ) )) # Int  |-> (1 * (i + 1 ) ))
  **  (IntArray.undef_seg out_pre (i + 1 ) n_pre )
  **  (IntArray.seg out_pre 0 i (sublist (0) (i) ((f_seq (n_pre)))) )
  **  ((( &( "p" ) )) # Int  |-> (1 * (i + 1 ) ))
  **  ((( &( "s" ) )) # Int  |-> (0 + (i + 1 ) ))
|--
  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n_pre) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  (IntArray.seg out_pre 0 (i + 1 ) (sublist (0) ((i + 1 )) ((f_seq (n_pre)))) )
  **  (IntArray.undef_seg out_pre (i + 1 ) n_pre )
  **  ((( &( "p" ) )) # Int  |-> 1)
  **  ((( &( "s" ) )) # Int  |-> 0)
.

Definition f_return_wit_1 := 
forall (out_pre: Z) (n_pre: Z) (i: Z) ,
  [| (i >= n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  (IntArray.seg out_pre 0 i (sublist (0) (i) ((f_seq (n_pre)))) )
  **  (IntArray.undef_seg out_pre i n_pre )
|--
  (IntArray.full out_pre n_pre (f_seq (n_pre)) )
.

Definition f_partial_solve_wit_1 := 
forall (out_pre: Z) (n_pre: Z) (i: Z) ,
  [| (((i + 1 ) % ( 2 ) ) = 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  (IntArray.seg out_pre 0 i (sublist (0) (i) ((f_seq (n_pre)))) )
  **  (IntArray.undef_seg out_pre i n_pre )
|--
  [| (((i + 1 ) % ( 2 ) ) = 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  (((out_pre + (i * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg out_pre (i + 1 ) n_pre )
  **  (IntArray.seg out_pre 0 i (sublist (0) (i) ((f_seq (n_pre)))) )
.

Definition f_partial_solve_wit_2 := 
forall (out_pre: Z) (n_pre: Z) (i: Z) ,
  [| (((i + 1 ) % ( 2 ) ) <> 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  (IntArray.seg out_pre 0 i (sublist (0) (i) ((f_seq (n_pre)))) )
  **  (IntArray.undef_seg out_pre i n_pre )
|--
  [| (((i + 1 ) % ( 2 ) ) <> 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  (((out_pre + (i * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg out_pre (i + 1 ) n_pre )
  **  (IntArray.seg out_pre 0 i (sublist (0) (i) ((f_seq (n_pre)))) )
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_f_safety_wit_1 : f_safety_wit_1.
Axiom proof_of_f_safety_wit_2 : f_safety_wit_2.
Axiom proof_of_f_safety_wit_3 : f_safety_wit_3.
Axiom proof_of_f_safety_wit_4 : f_safety_wit_4.
Axiom proof_of_f_safety_wit_5 : f_safety_wit_5.
Axiom proof_of_f_safety_wit_6 : f_safety_wit_6.
Axiom proof_of_f_safety_wit_7 : f_safety_wit_7.
Axiom proof_of_f_safety_wit_8 : f_safety_wit_8.
Axiom proof_of_f_safety_wit_9 : f_safety_wit_9.
Axiom proof_of_f_safety_wit_10 : f_safety_wit_10.
Axiom proof_of_f_safety_wit_11 : f_safety_wit_11.
Axiom proof_of_f_safety_wit_12 : f_safety_wit_12.
Axiom proof_of_f_safety_wit_13 : f_safety_wit_13.
Axiom proof_of_f_safety_wit_14 : f_safety_wit_14.
Axiom proof_of_f_safety_wit_15 : f_safety_wit_15.
Axiom proof_of_f_safety_wit_16 : f_safety_wit_16.
Axiom proof_of_f_entail_wit_1 : f_entail_wit_1.
Axiom proof_of_f_entail_wit_2_1 : f_entail_wit_2_1.
Axiom proof_of_f_entail_wit_2_2 : f_entail_wit_2_2.
Axiom proof_of_f_return_wit_1 : f_return_wit_1.
Axiom proof_of_f_partial_solve_wit_1 : f_partial_solve_wit_1.
Axiom proof_of_f_partial_solve_wit_2 : f_partial_solve_wit_2.

End VC_Correct.
